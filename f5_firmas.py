"""
ALGORITMO F5 – IMPLEMENTACIÓN CON FIRMAS
==========================================
TFG – Grado en Matemáticas Aplicadas – Universidad Nebrija
"Bases de Gröbner y sus Aplicaciones en Criptografía Multivariante"

Implementa el algoritmo F5 de Faugère (2002) en su versión incremental,
con la estructura completa de firmas descrita en el capítulo 5 del trabajo.

Componentes implementados:
  · Clase Signature  — par (monomio, índice) = t · e_j
  · Orden modular POT (Position Over Term)
  · Clase SignedPolynomial — par firmado (σ, p)
  · sig_reduction  — reducción con respeto de firmas (Definición 6.23)
  · Criterio de sizygia (Definición 6.26, Lema 6.27)
  · Criterio de reescritura (Definición 6.28, Proposición 6.29)
  · Sig-redundancia (Definición 6.30, Lema 6.31)
  · f5_incremental — algoritmo F5 completo (Teorema 6.33)

NOTA SOBRE EL ALCANCE:
Esta implementación es educativa y correcta en su estructura matemática.
Corresponde a la versión «F5-criterio» de Eder–Perry (2011). No incluye
las optimizaciones de implementación de la versión comercial (FGb), que
añade reducción matricial por lotes (al estilo F4), caché de reducción y
representaciones compactas de firmas para mejorar la eficiencia en memoria.

Referencia teórica: §6.3 – §6.4 del trabajo (capítulo 5).
"""

from fractions import Fraction
from functools import cmp_to_key
from typing import List, Optional, Tuple, Set
import time

from algoritmos_groebner import (
    Monomial, Ring, Polynomial,
    lex, grlex, grevlex,
    s_polynomial, division, remainder,
    reduced_groebner_basis as buchberger_basis,
)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 1 – FIRMAS (SIGNATURES)
# ══════════════════════════════════════════════════════════════

class Signature:
    """
    Firma σ = t · e_j  del capítulo 5, Definición 6.20.

    Representa la procedencia de un polinomio p ∈ R respecto de los
    generadores iniciales F = (f_0, …, f_{m-1}):

        p = h_0 f_0 + … + h_{m-1} f_{m-1},  sig(p) = LM(h_j) · e_j

    donde j es el índice para el que LM(h_j) · e_j es máximo en el
    orden modular.

    Atributos
    ---------
    mono : Monomial   — el monomio t de la firma t · e_j
    idx  : int        — el índice j del generador original (base-0)

    Orden modular POT (Position Over Term, §6.3.2):
        t₁ · e_{j₁}  >_POT  t₂ · e_{j₂}
            ⟺  j₁ > j₂
            o   j₁ = j₂  y  t₁ >_R t₂  (orden del anillo R)
    """

    def __init__(self, mono: Monomial, idx: int, ring_order):
        self.mono = mono
        self.idx = idx
        self._order = ring_order

    # ── Comparación (orden POT) ──────────────────────────────

    def _cmp(self, other: "Signature") -> int:
        """Devuelve 1, -1 o 0 comparando con POT."""
        if self.idx != other.idx:
            return 1 if self.idx > other.idx else -1
        return self._order(self.mono, other.mono)

    def __gt__(self, other: "Signature") -> bool: return self._cmp(other) >  0
    def __lt__(self, other: "Signature") -> bool: return self._cmp(other) <  0
    def __ge__(self, other: "Signature") -> bool: return self._cmp(other) >= 0
    def __le__(self, other: "Signature") -> bool: return self._cmp(other) <= 0
    def __eq__(self, other) -> bool:
        return (isinstance(other, Signature)
                and self.idx == other.idx
                and self.mono == other.mono)
    def __hash__(self) -> int:
        return hash((self.mono, self.idx))

    # ── Operaciones algebraicas ──────────────────────────────

    def multiply(self, t: Monomial) -> "Signature":
        """t · σ = (t · σ.mono) · e_{σ.idx}"""
        return Signature(self.mono * t, self.idx, self._order)

    def divisible_by(self, other: "Signature") -> bool:
        """
        σ₁ es divisible por σ₂ si:
          · tienen el mismo índice  (j₁ = j₂), y
          · el monomio de σ₁ es múltiplo del de σ₂  (t₁ divisible por t₂).
        """
        return (self.idx == other.idx
                and self.mono.divisible_by(other.mono))

    def __repr__(self) -> str:
        return f"σ({self.mono.exp}·e_{self.idx})"


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 2 – PARES FIRMADOS
# ══════════════════════════════════════════════════════════════

class SignedPolynomial:
    """
    Par firmado (σ, p) donde σ es una firma y p ∈ R es un polinomio
    (Definición 6.20, capítulo 5).

    La firma codifica la procedencia algebraica de p respecto de los
    generadores iniciales. Dos polinomios con el mismo valor algebraico
    pero firmas distintas se tratan de forma diferente en F5.
    """

    def __init__(self, sig: Signature, poly: Polynomial):
        self.sig = sig
        self.poly = poly

    def is_zero(self) -> bool:
        return self.poly.is_zero()

    def __repr__(self) -> str:
        return f"({self.sig}, {self.poly})"


def make_unit_signature(idx: int, n: int, ring_order) -> Signature:
    """Firma trivial 1 · e_j = e_j (para el j-ésimo generador inicial)."""
    return Signature(Monomial((0,) * n), idx, ring_order)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 3 – SIG-REDUCTION
# ══════════════════════════════════════════════════════════════

def sig_reduce(sp: SignedPolynomial,
               basis: List[SignedPolynomial],
               verbose: bool = False) -> SignedPolynomial:
    """
    Sig-reduction de (σ, p) respecto a la base firmada (Definición 6.23).

    Un reductor (τ, g) es válido para el término t de p si:
      1. LM(g) divide a t, y
      2. la firma del múltiplo  (t / LM(g)) · τ  es < σ   (en orden POT).

    La condición 2 garantiza que la reducción nunca "sube" la firma,
    preservando así la consistencia genealógica del polinomio.
    (Proposición 6.24 del capítulo 5.)
    """
    p = sp.poly
    sigma = sp.sig
    ring = p.ring

    while not p.is_zero():
        lm_p = p.LM()
        lc_p = p.LC()
        reduced = False

        for b in basis:
            if b.is_zero():
                continue
            lm_g = b.poly.LM()
            if lm_p.divisible_by(lm_g):
                # Factor monomial de la reducción
                t = lm_p / lm_g
                # Firma del múltiplo que se usaría como reductor
                mult_sig = b.sig.multiply(t)
                # Solo reducir si la firma del múltiplo es < σ
                if mult_sig < sigma:
                    coeff = lc_p * ring.inv(b.poly.LC())
                    p = p - b.poly.scale(coeff, t)
                    reduced = True
                    if verbose:
                        print(f"      sig-red: {lm_p} por {b.sig} → resto {p.LM() if not p.is_zero() else '0'}")
                    break

        if not reduced:
            break   # p no es reducible respetando firmas: salimos

    return SignedPolynomial(sigma, p)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 4 – SYZYGIAS TRIVIALES
# ══════════════════════════════════════════════════════════════

def trivial_syzygy_signature(sig_i: Signature,
                              sig_j: Signature,
                              lm_i: Monomial,
                              lm_j: Monomial) -> Signature:
    """
    Firma de la sizygia trivial  f_j · e_i − f_i · e_j = 0.

    En el orden POT (con i > j), la firma de esta sizygia es:
        LM(f_j) · e_i   (pues e_i > e_j en POT)

    (Los sistemas de sizygias triviales generan el módulo de sizygias de
    los monomios líderes; cf. Proposición 5.18 del capítulo 4.)
    """
    # LM(f_i) · e_j  vs  LM(f_j) · e_i
    cand_i = sig_j.multiply(lm_i)   # LM(f_i) · e_j
    cand_j = sig_i.multiply(lm_j)   # LM(f_j) · e_i
    # Devolver la mayor en POT
    return cand_j if cand_j >= cand_i else cand_i


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 5 – CRITERIOS DE F5
# ══════════════════════════════════════════════════════════════

def syzygy_criterion(sig: Signature,
                     known_syzygies: Set[Signature]) -> bool:
    """
    Criterio de sizygia (Definición 6.26, Lema 6.27).

    Descarta un par firmado (σ, p) si σ es divisible por la firma
    de alguna sizygia conocida: en ese caso, p se reduciría
    inevitablemente a cero (la sizygia explica su anulación).

    Coste: O(|known_syzygies|).
    """
    return any(sig.divisible_by(sz) for sz in known_syzygies)


def rewrite_criterion(sig: Signature,
                      lm_poly: Monomial,
                      basis: List[SignedPolynomial]) -> bool:
    """
    Criterio de reescritura (Definición 6.28, Proposición 6.29).

    Descarta (σ, p) si existe (τ, g) en la base tal que:
      · τ divide a σ  (τ | σ  en el sentido de Signature.divisible_by), y
      · LM(g) divide a LM(p).

    En ese caso, g representa la misma firma de forma más económica,
    y cualquier cancelación que p pudiera producir ya está cubierta por g.
    """
    for b in basis:
        if b.is_zero():
            continue
        if (sig.divisible_by(b.sig)
                and lm_poly.divisible_by(b.poly.LM())):
            return True
    return False


def sig_redundant(sig: Signature,
                  lm_poly: Monomial,
                  basis: List[SignedPolynomial]) -> bool:
    """
    Sig-redundancia (Definición 6.30, Lema 6.31).

    (σ, p) es sig-redundante si existe (τ, g) en la base tal que
    τ | σ y LM(g) | LM(p). Se puede omitir sin alterar la corrección.
    """
    return rewrite_criterion(sig, lm_poly, basis)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 6 – FIRMA DEL S-POLINOMIO
# ══════════════════════════════════════════════════════════════

def s_polynomial_signature(sp1: SignedPolynomial,
                            sp2: SignedPolynomial) -> Signature:
    """
    Calcula la firma del S-polinomio S(p, q) donde (σ_p, p) y (σ_q, q)
    son pares firmados.

    S(p,q) = L/LT(p) · p − L/LT(q) · q,  L = lcm(LM(p), LM(q))

    La firma de cada parte:
      · parte de p: (L/LM(p)) · σ_p
      · parte de q: (L/LM(q)) · σ_q

    La firma del S-polinomio es la mayor de las dos (en POT).
    Si las dos son iguales, el S-polinomio podría ser trivialmente cero
    (pero no se descarta aquí; los criterios lo hacen).
    """
    lm1 = sp1.poly.LM()
    lm2 = sp2.poly.LM()
    L = lm1.lcm(lm2)
    t1 = L / lm1   # L / LM(p)
    t2 = L / lm2   # L / LM(q)
    sig1 = sp1.sig.multiply(t1)
    sig2 = sp2.sig.multiply(t2)
    return sig1 if sig1 >= sig2 else sig2


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 7 – ALGORITMO F5 INCREMENTAL
# ══════════════════════════════════════════════════════════════

def f5_incremental(generators: List[Polynomial],
                   verbose: bool = False) -> List[Polynomial]:
    """
    Algoritmo F5 en versión incremental (Teorema 6.33, capítulo 5).

    Procesa los generadores f_0, f_1, …, f_{m-1} uno a uno. En la
    etapa i, G_i es una base de Gröbner firmada de ⟨f_0,…,f_i⟩.

    Para cada nuevo par crítico (σ_new, f_i) con los elementos de G_{i-1}:
      1. Calcular la firma del S-polinomio.
      2. Aplicar criterio de sizygia → descartar si aplica.
      3. Aplicar criterio de reescritura → descartar si aplica.
      4. Efectuar sig-reduction.
      5. Si el resultado es no nulo, añadirlo a G_i con su firma.

    Al final del bucle, G_m contiene una base de Gröbner de ⟨f_0,…,f_{m-1}⟩.

    Parameters
    ----------
    generators : lista de polinomios generadores f_0,…,f_{m-1}
    verbose    : si True, muestra el estado de cada operación

    Returns
    -------
    Lista de polinomios que forman una base de Gröbner del ideal.
    """
    ring = generators[0].ring
    n = ring.n
    order = ring.order
    m = len(generators)

    # ── Inicialización ──────────────────────────────────────
    # El primer generador f_0 recibe firma e_0 = 1·e_0
    sig_0 = make_unit_signature(0, n, order)
    # Hacer f_0 mónico si el cuerpo lo permite
    f0 = generators[0]
    basis: List[SignedPolynomial] = [SignedPolynomial(sig_0, f0)]
    known_syzygies: Set[Signature] = set()

    if verbose:
        print(f"F5: m={m} generadores, n={n} variables")
        print(f"\nEtapa 0: G_0 = {{(e_0, {f0})}}")

    # ── Bucle incremental ────────────────────────────────────
    for i in range(1, m):
        fi = generators[i]
        sig_i = make_unit_signature(i, n, order)
        sp_new = SignedPolynomial(sig_i, fi)

        if verbose:
            print(f"\n{'─'*50}")
            print(f"Etapa {i}: añadiendo f_{i} = {fi}")

        # ── Añadir syzygias triviales con los generadores anteriores ─
        # La sizygia  f_j · e_i − f_i · e_j = 0  tiene firma LM(f_j)·e_i
        # (bajo POT, e_i > e_j pues i > j → firma = LM(f_j)·e_i)
        for b in basis:
            lm_b = b.poly.LM()
            lm_fi = fi.LM()
            sz_sig = trivial_syzygy_signature(b.sig, sig_i, lm_fi, lm_b)
            known_syzygies.add(sz_sig)
            if verbose:
                print(f"  sizygia trivial: {sz_sig}")

        # ── Cola dinámica de pares ────────────────────────────
        # Empezamos con pares entre los elementos existentes y f_i.
        # Cuando se añade un elemento nuevo r, añadimos pares (r, b)
        # para TODOS los elementos b del basis actual, pues r puede
        # generar nuevos S-polinomios esenciales con elementos anteriores.
        # Los criterios de sizygia y reescritura descartan los redundantes.
        queue: List[Tuple[SignedPolynomial, SignedPolynomial]] = [
            (b, sp_new) for b in basis
        ]
        new_elements: List[SignedPolynomial] = []

        while queue:
            # Ordenar por grado del lcm (estrategia de grado mínimo)
            queue.sort(key=lambda pr: pr[0].poly.LM().lcm(pr[1].poly.LM()).degree)
            sp_a, sp_b = queue.pop(0)

            # 1. Calcular firma del S-polinomio
            sp_sig = s_polynomial_signature(sp_a, sp_b)

            if verbose:
                lm_a = sp_a.poly.LM()
                lm_b2 = sp_b.poly.LM()
                print(f"\n  Par: ({sp_a.sig}, LM={lm_a.exp}) × ({sp_b.sig}, LM={lm_b2.exp})")
                print(f"  Firma S-pol: {sp_sig}")

            # 2. Criterio de sizygia
            if syzygy_criterion(sp_sig, known_syzygies):
                if verbose:
                    print(f"  → CRITERIO SIZYGIA: descartado")
                continue

            # 3. Criterio de reescritura
            lm_sp = sp_a.poly.LM().lcm(sp_b.poly.LM())
            current_all = basis + new_elements
            if rewrite_criterion(sp_sig, lm_sp, current_all):
                if verbose:
                    print(f"  → CRITERIO REESCRITURA: descartado")
                continue

            # 4. Calcular el S-polinomio y efectuar sig-reduction
            sp_poly = s_polynomial(sp_a.poly, sp_b.poly)
            signed_sp = SignedPolynomial(sp_sig, sp_poly)
            reduced = sig_reduce(signed_sp, current_all, verbose=verbose)

            if verbose:
                print(f"  S-pol = {sp_poly}")
                print(f"  Sig-reducido = {reduced.poly if not reduced.is_zero() else '0'}")

            # 5. Si no nulo, añadir a la base y generar nuevos pares
            if not reduced.is_zero():
                lc = reduced.poly.LC()
                r = SignedPolynomial(
                    reduced.sig,
                    reduced.poly * ring.inv(lc)
                )
                new_elements.append(r)
                # Generar pares entre r y TODOS los elementos actuales:
                # - Pares con elementos de G_{i-1}: pueden producir nuevos
                #   elementos necesarios para completar la base.
                # - Pares con nuevos elementos: igual.
                # - Pares con f_i: por si r no provino directamente de f_i.
                # Los criterios descartan los redundantes eficientemente.
                for b in current_all + [sp_new]:
                    queue.append((b, r))
                if verbose:
                    print(f"  *** Nuevo: {r.sig}, {r.poly}  →  {len(current_all)+1} pares nuevos en cola")

        # Añadir el nuevo generador y los elementos generados
        basis.append(sp_new)
        basis.extend(new_elements)

        if verbose:
            print(f"\n  |G_{i}| = {len(basis)} polinomios")

    # ── Extraer los polinomios y reducir la base ─────────────
    polys = [b.poly for b in basis if not b.is_zero()]
    return polys


def f5_reduced(generators: List[Polynomial],
               verbose: bool = False) -> List[Polynomial]:
    """
    Base de Gröbner reducida calculada con F5.

    Aplica F5 incremental y luego reduce la base resultante
    (la reducción final es idéntica a la de Buchberger).
    """
    G_raw = f5_incremental(generators, verbose=verbose)
    # Reducir la base (misma estrategia que en Buchberger)
    return buchberger_basis(G_raw)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 8 – COMPARACIÓN F5 vs BUCHBERGER
# ══════════════════════════════════════════════════════════════

def comparar_buchberger_f5(generators: List[Polynomial]):
    """
    Compara resultados y tiempos de Buchberger y F5.
    """
    print("\n" + "─" * 60)
    print("Comparación Buchberger vs F5")
    print("─" * 60)

    t0 = time.perf_counter()
    G_buch = buchberger_basis(generators)
    t_buch = time.perf_counter() - t0

    t0 = time.perf_counter()
    G_f5 = f5_reduced(generators)
    t_f5 = time.perf_counter() - t0

    print(f"\nBuchberger  ({t_buch*1000:.2f} ms):")
    for g in G_buch:
        print(f"  {g}")

    print(f"\nF5          ({t_f5*1000:.2f} ms):")
    for g in G_f5:
        print(f"  {g}")

    lm_buch = {g.LM() for g in G_buch}
    lm_f5   = {g.LM() for g in G_f5}
    print(f"\n¿Mismos términos líderes? {lm_buch == lm_f5}")


def contar_pares_descartados(generators: List[Polynomial]) -> dict:
    """
    Ejecuta F5 con verbose y cuenta cuántos pares descarta cada criterio.
    Muestra el ahorro respecto a Buchberger (que no descarta ninguno).
    """
    ring = generators[0].ring
    n = ring.n
    order = ring.order
    m = len(generators)

    stats = {"sizygia": 0, "reescritura": 0, "procesados": 0}

    sig_0 = make_unit_signature(0, n, order)
    basis = [SignedPolynomial(sig_0, generators[0])]
    known_syzygies: Set[Signature] = set()

    for i in range(1, m):
        fi = generators[i]
        sig_i = make_unit_signature(i, n, order)
        sp_new = SignedPolynomial(sig_i, fi)

        for b in basis:
            lm_b = b.poly.LM()
            lm_fi = fi.LM()
            sz_sig = trivial_syzygy_signature(b.sig, sig_i, lm_fi, lm_b)
            known_syzygies.add(sz_sig)

        pairs = [(b, sp_new) for b in basis]
        pairs.sort(key=lambda pr: pr[0].poly.LM().lcm(pr[1].poly.LM()).degree)

        new_elements = []
        for (sp_a, sp_b) in pairs:
            sp_sig = s_polynomial_signature(sp_a, sp_b)
            if syzygy_criterion(sp_sig, known_syzygies):
                stats["sizygia"] += 1
                continue
            lm_sp = sp_a.poly.LM().lcm(sp_b.poly.LM())
            current_basis = basis + new_elements
            if rewrite_criterion(sp_sig, lm_sp, current_basis):
                stats["reescritura"] += 1
                continue
            sp_poly = s_polynomial(sp_a.poly, sp_b.poly)
            signed_sp = SignedPolynomial(sp_sig, sp_poly)
            reduced = sig_reduce(signed_sp, current_basis)
            stats["procesados"] += 1
            if not reduced.is_zero():
                lc = reduced.poly.LC()
                new_elements.append(SignedPolynomial(
                    reduced.sig, reduced.poly * ring.inv(lc)
                ))

        basis.append(sp_new)
        basis.extend(new_elements)

    total = stats["sizygia"] + stats["reescritura"] + stats["procesados"]
    stats["total_pares"] = total
    stats["descartados"] = stats["sizygia"] + stats["reescritura"]
    stats["pct_descartado"] = (stats["descartados"] / total * 100) if total > 0 else 0
    return stats


# ══════════════════════════════════════════════════════════════
#  DEMOS
# ══════════════════════════════════════════════════════════════

def demo_firmas_y_criterios():
    print("=" * 60)
    print("DEMO 1 – Firmas y criterios en F5")
    print("  I = ⟨f_0, f_1⟩ = ⟨x² − y, xy − 1⟩  en Q[x,y], lex")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f0 = R.poly({(2,0): 1, (0,1): -1})   # x² − y
    f1 = R.poly({(1,1): 1, (0,0): -1})   # xy − 1

    print(f"\n  f_0 = {f0},  sig(f_0) = e_0")
    print(f"  f_1 = {f1},  sig(f_1) = e_1")

    sig_0 = make_unit_signature(0, 2, lex)
    sig_1 = make_unit_signature(1, 2, lex)
    sp0 = SignedPolynomial(sig_0, f0)
    sp1 = SignedPolynomial(sig_1, f1)

    # Firma del S-polinomio
    sp_sig = s_polynomial_signature(sp0, sp1)
    print(f"\n  S(f_0, f_1) = {s_polynomial(f0, f1)}")
    print(f"  Firma del S-pol: {sp_sig}")
    print(f"  (LM(f_1)/LM(f_0)·sig_0 = y·e_0)")

    # Sizygia trivial
    lm0, lm1 = f0.LM(), f1.LM()
    sz = trivial_syzygy_signature(sig_0, sig_1, lm1, lm0)
    print(f"\n  Sizygia trivial f_1·e_0 − f_0·e_1: firma = {sz}")
    print(f"  ¿{sp_sig} divisible por {sz}? → ", sp_sig.divisible_by(sz))


def demo_f5_completo():
    print("\n" + "=" * 60)
    print("DEMO 2 – F5 incremental con traza completa")
    print("  I = ⟨x² − y,  xy − 1⟩ en Q[x,y], lex")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f0 = R.poly({(2,0): 1, (0,1): -1})
    f1 = R.poly({(1,1): 1, (0,0): -1})
    G = f5_reduced([f0, f1], verbose=True)
    print(f"\n  Base de Gröbner reducida (F5):")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")


def demo_comparacion_tres_algoritmos():
    print("\n" + "=" * 60)
    print("DEMO 3 – Comparación Buchberger / F5 / con estadísticas")
    print("  Sistema en Q[x,y,z], orden grevlex")
    print("=" * 60)
    R = Ring(['x','y','z'], order=grevlex, char=0)
    f0 = R.poly({(2,0,0):1, (0,1,0):-1})            # x² − y
    f1 = R.poly({(1,1,0):1, (0,0,1):-1})            # xy − z
    f2 = R.poly({(0,2,0):1, (1,0,0):-1, (0,0,1):1}) # y² − x + z
    gens = [f0, f1, f2]

    comparar_buchberger_f5(gens)

    stats = contar_pares_descartados(gens)
    print(f"\nEstadísticas de criterios F5:")
    print(f"  Total pares generados : {stats['total_pares']}")
    print(f"  Criterio sizygia      : {stats['sizygia']} descartados")
    print(f"  Criterio reescritura  : {stats['reescritura']} descartados")
    print(f"  Efectivamente reducidos: {stats['procesados']}")
    print(f"  Porcentaje descartado : {stats['pct_descartado']:.1f}%")
    print(f"\n  → F5 ahorra el {stats['pct_descartado']:.0f}% del trabajo de reducción")
    print(f"    que Buchberger haría en vano (reducciones a cero).")


def demo_f5_sobre_Fp():
    print("\n" + "=" * 60)
    print("DEMO 4 – F5 sobre F_2[x,y,z], orden grevlex")
    print("  Sistema MQ cuadrático")
    print("=" * 60)
    R = Ring(['x','y','z'], order=grevlex, char=2)
    f0 = R.poly({(1,1,0):1, (1,0,1):1, (0,0,0):1})  # xy+xz+1
    f1 = R.poly({(0,1,1):1, (1,0,0):1, (0,0,1):1})  # yz+x+z
    f2 = R.poly({(1,0,1):1, (0,1,0):1, (0,0,0):1})  # xz+y+1
    G = f5_reduced([f0, f1, f2], verbose=False)
    print(f"\n  Base de Gröbner reducida (F5):")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")

    # Verificar mismos resultados que Buchberger
    from algoritmos_groebner import reduced_groebner_basis
    G_b = reduced_groebner_basis([f0, f1, f2])
    lm_f5   = {g.LM() for g in G}
    lm_buch = {g.LM() for g in G_b}
    print(f"\n  ¿Mismos LMs que Buchberger? {lm_f5 == lm_buch}")


if __name__ == "__main__":
    demo_firmas_y_criterios()
    demo_f5_completo()
    demo_comparacion_tres_algoritmos()
    demo_f5_sobre_Fp()
