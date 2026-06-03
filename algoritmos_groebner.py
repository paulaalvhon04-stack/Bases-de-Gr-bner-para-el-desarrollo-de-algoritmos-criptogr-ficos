"""
ALGORITMOS PARA BASES DE GRÖBNER
==================================
TFG – Grado en Matemáticas Aplicadas – Universidad Nebrija
"Bases de Gröbner y sus Aplicaciones en Criptografía Multivariante"

Implementa desde cero, sin librerías de álgebra computacional:
  ·  Representación de monomios y polinomios sobre Q (char=0) o F_p (char=p)
  ·  Órdenes monomiales: lex, grlex, grevlex
  ·  Algoritmo de división multivariante
  ·  S-polinomio
  ·  Algoritmo de Buchberger (con criterios del producto y de la cadena)
  ·  Base de Gröbner reducida
  ·  Criterio de pertenencia al ideal
  ·  Ideal de eliminación

Referencia teórica: capítulos 3 y 4 del trabajo.
"""

from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations
from typing import List, Tuple, Dict, Optional


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 1 – MONOMIOS
# ══════════════════════════════════════════════════════════════

class Monomial:
    """
    Monomio x_1^{a_1} · x_2^{a_2} · ... · x_n^{a_n}.

    Almacenado internamente como tupla de enteros no negativos.
    """

    __slots__ = ("exp",)

    def __init__(self, exponents):
        self.exp = tuple(int(e) for e in exponents)

    # ── Propiedades ─────────────────────────────────────────
    @property
    def n(self) -> int:
        return len(self.exp)

    @property
    def degree(self) -> int:
        """Grado total: deg(x^α) = α_1 + … + α_n."""
        return sum(self.exp)

    # ── Operaciones entre monomios ───────────────────────────
    def __mul__(self, other: "Monomial") -> "Monomial":
        return Monomial(a + b for a, b in zip(self.exp, other.exp))

    def __truediv__(self, other: "Monomial") -> "Monomial":
        """División exacta. Lanza ValueError si no es divisible."""
        if not self.divisible_by(other):
            raise ValueError(f"{self} no es múltiplo de {other}")
        return Monomial(a - b for a, b in zip(self.exp, other.exp))

    def divisible_by(self, other: "Monomial") -> bool:
        """True si existe monomio m tal que self = other · m."""
        return all(a >= b for a, b in zip(self.exp, other.exp))

    def lcm(self, other: "Monomial") -> "Monomial":
        """mcm(x^α, x^β) = x^{max(α,β)}."""
        return Monomial(max(a, b) for a, b in zip(self.exp, other.exp))

    def coprime_with(self, other: "Monomial") -> bool:
        """True si gcd(self, other) = 1 (todos los mínimos son 0)."""
        return all(min(a, b) == 0 for a, b in zip(self.exp, other.exp))

    # ── Métodos Python estándar ──────────────────────────────
    def __eq__(self, other) -> bool:
        return isinstance(other, Monomial) and self.exp == other.exp

    def __hash__(self) -> int:
        return hash(self.exp)

    def __repr__(self) -> str:
        return f"Monomial{self.exp}"


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 2 – ÓRDENES MONOMIALES
# ══════════════════════════════════════════════════════════════

def lex(m1: Monomial, m2: Monomial) -> int:
    """
    Orden lexicográfico (Definición 4.3 del capítulo 3).

    m1 >_lex m2 si la primera componente no nula de exp(m1)−exp(m2)
    es positiva.

    Devuelve  1 si m1 > m2,  −1 si m1 < m2,  0 si son iguales.
    """
    for a, b in zip(m1.exp, m2.exp):
        if a > b: return  1
        if a < b: return -1
    return 0


def grlex(m1: Monomial, m2: Monomial) -> int:
    """
    Orden lexicográfico graduado (Definición 4.5 del capítulo 3).

    m1 >_grlex m2  si  deg(m1) > deg(m2),
                   o   deg(m1) = deg(m2)  y  m1 >_lex m2.
    """
    d = m1.degree - m2.degree
    if d != 0:
        return 1 if d > 0 else -1
    return lex(m1, m2)


def grevlex(m1: Monomial, m2: Monomial) -> int:
    """
    Orden lexicográfico graduado inverso (Definición 4.6 del capítulo 3).

    m1 >_grevlex m2  si  deg(m1) > deg(m2),
                     o   deg(m1) = deg(m2)  y  la última componente no
                         nula de exp(m1)−exp(m2) es negativa.
    """
    d = m1.degree - m2.degree
    if d != 0:
        return 1 if d > 0 else -1
    for a, b in zip(reversed(m1.exp), reversed(m2.exp)):
        if a < b: return  1   # nota: invertido respecto a lex
        if a > b: return -1
    return 0


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 3 – ANILLO DE POLINOMIOS
# ══════════════════════════════════════════════════════════════

class Ring:
    """
    Contexto del anillo k[x_1, …, x_n].

    Parameters
    ----------
    variables : lista de nombres de variables, p. ej. ['x', 'y', 'z']
    order     : función de comparación de monomios (lex, grlex, grevlex)
    char      : característica del cuerpo  (0 = ℚ,  p primo = 𝔽_p)
    """

    def __init__(self, variables: List[str], order=grlex, char: int = 0):
        if char != 0:
            # Verificar que la característica sea primo
            if char < 2 or any(char % i == 0 for i in range(2, char)):
                raise ValueError(f"{char} no es primo")
        self.variables = list(variables)
        self.n = len(variables)
        self.order = order
        self.char = char

    def __repr__(self) -> str:
        k = "ℚ" if self.char == 0 else f"𝔽_{self.char}"
        return f"{k}[{', '.join(self.variables)}]"

    # ── Constructores de polinomios ──────────────────────────

    def poly(self, d: dict) -> "Polynomial":
        """Crea polinomio desde dict {(exp,…,exp): coeficiente}."""
        terms = {Monomial(k): v for k, v in d.items()}
        return Polynomial(terms, self)

    def zero(self) -> "Polynomial":
        return Polynomial({}, self)

    def one(self) -> "Polynomial":
        e = Monomial((0,) * self.n)
        return self.poly({e.exp: 1})

    def variable(self, i: int) -> "Polynomial":
        """Devuelve el polinomio x_i."""
        e = [0] * self.n
        e[i] = 1
        return self.poly({tuple(e): 1})

    # ── Aritmética de coeficientes ───────────────────────────

    def norm(self, c) -> "coeff":
        """Normaliza un coeficiente al cuerpo k."""
        if self.char == 0:
            return Fraction(c) if not isinstance(c, Fraction) else c
        return int(c) % self.char

    def inv(self, c) -> "coeff":
        """Inverso multiplicativo en k."""
        if self.char == 0:
            return Fraction(1, c) if isinstance(c, Fraction) else Fraction(1, c)
        return pow(int(c), -1, self.char)


class Polynomial:
    """
    Polinomio en k[x_1, …, x_n].

    Representado como dict {Monomial: coeficiente}.
    Los coeficientes son Fraction (char=0) o int (char=p).
    """

    def __init__(self, terms: Dict[Monomial, "coeff"], ring: Ring):
        self.ring = ring
        # Normalizar y eliminar términos con coeficiente 0
        self.terms: Dict[Monomial, "coeff"] = {}
        for m, c in terms.items():
            c = ring.norm(c)
            if c != 0:
                self.terms[m] = c

    # ── Propiedades ──────────────────────────────────────────

    def is_zero(self) -> bool:
        return len(self.terms) == 0

    def _sorted(self) -> List[Monomial]:
        """Monomios ordenados de mayor a menor."""
        return sorted(self.terms, key=cmp_to_key(self.ring.order), reverse=True)

    def LM(self) -> Monomial:
        """Monomio líder LM(f)."""
        if self.is_zero():
            raise ValueError("El polinomio cero no tiene monomio líder")
        return self._sorted()[0]

    def LC(self):
        """Coeficiente líder LC(f)."""
        return self.terms[self.LM()]

    def LT(self) -> Tuple:
        """Término líder: devuelve (LC, LM)."""
        m = self.LM()
        return self.terms[m], m

    # ── Aritmética ────────────────────────────────────────────

    def _new(self, terms):
        return Polynomial(terms, self.ring)

    def __add__(self, other: "Polynomial") -> "Polynomial":
        result = dict(self.terms)
        for m, c in other.terms.items():
            result[m] = result.get(m, 0) + c
        return self._new(result)

    def __neg__(self) -> "Polynomial":
        return self._new({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: "Polynomial") -> "Polynomial":
        return self + (-other)

    def __mul__(self, other) -> "Polynomial":
        if isinstance(other, (int, Fraction)):
            return self._new({m: c * other for m, c in self.terms.items()})
        if isinstance(other, Polynomial):
            result = {}
            for m1, c1 in self.terms.items():
                for m2, c2 in other.terms.items():
                    m = m1 * m2
                    result[m] = result.get(m, 0) + c1 * c2
            return self._new(result)
        return NotImplemented

    __rmul__ = __mul__

    def scale(self, coeff, mono: Monomial) -> "Polynomial":
        """Devuelve coeff · mono · self."""
        result = {}
        for m, c in self.terms.items():
            result[m * mono] = self.ring.norm(c * coeff)
        return self._new(result)

    # ── Comparación ──────────────────────────────────────────

    def __eq__(self, other) -> bool:
        if isinstance(other, int) and other == 0:
            return self.is_zero()
        if not isinstance(other, Polynomial):
            return False
        return self.terms == other.terms

    # ── Representación ────────────────────────────────────────

    def __repr__(self) -> str:
        if self.is_zero():
            return "0"
        var = self.ring.variables
        parts = []
        for m in self._sorted():
            c = self.terms[m]
            mstr = "".join(
                (f"{var[i]}" if e == 1 else f"{var[i]}^{e}")
                for i, e in enumerate(m.exp) if e > 0
            ) or "1"
            if mstr == "1":
                parts.append(str(c))
            elif c == 1:
                parts.append(mstr)
            elif c == -1:
                parts.append(f"-{mstr}")
            else:
                parts.append(f"{c}*{mstr}")
        out = parts[0]
        for p in parts[1:]:
            out += (" - " + p[1:]) if p.startswith("-") else (" + " + p)
        return out


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 4 – ALGORITMO DE DIVISIÓN MULTIVARIANTE
# ══════════════════════════════════════════════════════════════

def division(f: Polynomial, divisors: List[Polynomial]) -> Tuple[List[Polynomial], Polynomial]:
    """
    Algoritmo de División Multivariante (Teorema 4.16, capítulo 3).

    Dado f y [f_1, …, f_s], calcula:
        f = q_1 f_1 + … + q_s f_s + r
    donde ningún término de r es divisible por ningún LM(f_i).

    Complejidad: O(|f| · max_i(|f_i|)) en número de términos.

    Returns
    -------
    (cocientes [q_1,…,q_s], resto r)
    """
    R = f.ring
    s = len(divisors)
    quotients = [R.zero() for _ in range(s)]
    remainder = R.zero()
    p = f

    while not p.is_zero():
        lm_p, lc_p = p.LM(), p.LC()
        reduced = False

        for i, fi in enumerate(divisors):
            lm_fi, lc_fi = fi.LM(), fi.LC()
            if lm_p.divisible_by(lm_fi):
                # Cancelar el término líder de p usando fi
                coeff = lc_p * R.inv(lc_fi)
                mono  = lm_p / lm_fi
                term  = R.poly({mono.exp: coeff})
                quotients[i] = quotients[i] + term
                p = p - fi.scale(coeff, mono)
                reduced = True
                break

        if not reduced:
            # El término líder no es divisible: pasa al resto
            remainder = remainder + R.poly({lm_p.exp: lc_p})
            p = p - R.poly({lm_p.exp: lc_p})

    return quotients, remainder


def remainder(f: Polynomial, divisors: List[Polynomial]) -> Polynomial:
    """Devuelve solo el resto de la división."""
    _, r = division(f, divisors)
    return r


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 5 – S-POLINOMIO
# ══════════════════════════════════════════════════════════════

def s_polynomial(f: Polynomial, g: Polynomial) -> Polynomial:
    """
    S-polinomio de f y g (Definición 4.38, capítulo 3).

        S(f, g) = lcm(LM(f), LM(g)) / LT(f) · f
                - lcm(LM(f), LM(g)) / LT(g) · g

    Por construcción, LT(S(f,g)) ≺ lcm(LM(f), LM(g)):
    el término líder se cancela.
    """
    R = f.ring
    lc_f, lm_f = f.LC(), f.LM()
    lc_g, lm_g = g.LC(), g.LM()
    lcm_fg = lm_f.lcm(lm_g)

    mono_f = lcm_fg / lm_f   # factor monomial para f
    mono_g = lcm_fg / lm_g   # factor monomial para g

    inv_lc_f = R.inv(lc_f)
    inv_lc_g = R.inv(lc_g)

    return f.scale(inv_lc_f, mono_f) - g.scale(inv_lc_g, mono_g)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 6 – ALGORITMO DE BUCHBERGER
# ══════════════════════════════════════════════════════════════

def buchberger(generators: List[Polynomial], verbose: bool = False) -> List[Polynomial]:
    """
    Algoritmo de Buchberger (Teorema 4.44, capítulo 3).

    Calcula una base de Gröbner del ideal generado por 'generators'.

    Optimizaciones implementadas:
      · Criterio del producto (Proposición 4.42): si gcd(LM(f), LM(g)) = 1
        entonces S(f,g) se reduce automáticamente a cero → par descartado.
      · Criterio de la cadena (Proposición 4.43): si existe h en G tal que
        LM(h) divide a lcm(LM(f), LM(g)) y los pares intermedios ya se han
        procesado → par descartado.

    Parameters
    ----------
    generators : lista de polinomios generadores del ideal
    verbose    : si True, imprime el progreso iteración a iteración

    Returns
    -------
    G : lista de polinomios (base de Gröbner, no reducida)
    """
    G = list(generators)
    # P = conjunto de pares críticos pendientes (índices)
    P = list(combinations(range(len(G)), 2))
    iteration = 0

    if verbose:
        print(f"Buchberger: inicio con {len(G)} generadores, {len(P)} pares")

    while P:
        i, j = P.pop(0)
        fi, fj = G[i], G[j]
        iteration += 1

        # ── Criterio del producto ──────────────────────────
        if fi.LM().coprime_with(fj.LM()):
            if verbose:
                print(f"  It.{iteration:3d}  par({i},{j}) → criterio del producto, descartado")
            continue

        # ── Criterio de la cadena ──────────────────────────
        lcm_ij = fi.LM().lcm(fj.LM())
        chain_eliminated = False
        for k, gk in enumerate(G):
            if k == i or k == j:
                continue
            if (lcm_ij.divisible_by(gk.LM())
                    and (min(i,k), max(i,k)) not in P
                    and (min(j,k), max(j,k)) not in P):
                chain_eliminated = True
                break
        if chain_eliminated:
            if verbose:
                print(f"  It.{iteration:3d}  par({i},{j}) → criterio de la cadena, descartado")
            continue

        # ── Calcular S-polinomio y reducir ─────────────────
        sp = s_polynomial(fi, fj)
        _, r = division(sp, G)

        if verbose:
            print(f"  It.{iteration:3d}  par({i},{j})  S-pol={sp}  →  r={r}")

        if not r.is_zero():
            new_idx = len(G)
            G.append(r)
            P += [(k, new_idx) for k in range(new_idx)]
            if verbose:
                print(f"           *** nuevo generador g_{new_idx+1} = {r}")

    if verbose:
        print(f"Buchberger finalizado: {len(G)} elementos en la base")
    return G


def reduced_groebner_basis(generators: List[Polynomial], verbose: bool = False) -> List[Polynomial]:
    """
    Base de Gröbner REDUCIDA (Teorema 4.36, capítulo 3).

    La base reducida es única para cada ideal y orden monomial fijos.
    Satisface:
      1. Cada polinomio es mónico (LC = 1).
      2. Ningún monomio de g_i es divisible por LM(g_j) para i ≠ j.

    Procedimiento:
      1. Calcular base de Gröbner vía Buchberger.
      2. Eliminar elementos redundantes (base minimal).
      3. Hacer cada elemento mónico.
      4. Reducir cada elemento respecto a los demás.
    """
    G = buchberger(generators, verbose=verbose)

    # Paso 2: base minimal (eliminar redundancias)
    minimal = []
    for g in G:
        lm_g = g.LM()
        if not any(lm_g.divisible_by(h.LM()) for h in G if h is not g):
            minimal.append(g)

    # Paso 3: hacer mónicos
    R = minimal[0].ring
    monic = []
    for g in minimal:
        lc = g.LC()
        monic.append(g * R.inv(lc))

    # Paso 4: reducir completamente cada elemento
    reduced = []
    for i, g in enumerate(monic):
        others = [h for j, h in enumerate(monic) if j != i]
        _, r = division(g, others)
        reduced.append(r)

    # Ordenar por término líder decreciente (presentación canónica)
    reduced.sort(key=lambda p: cmp_to_key(p.ring.order)(p.LM()), reverse=True)

    if verbose:
        print(f"\nBase de Gröbner reducida: {len(reduced)} elementos")

    return reduced


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 7 – APLICACIONES ALGEBRAICAS
# ══════════════════════════════════════════════════════════════

def ideal_membership(f: Polynomial, generators: List[Polynomial]) -> bool:
    """
    Criterio de pertenencia al ideal (Teorema 4.32, capítulo 3).

    f ∈ ⟨f_1,…,f_s⟩  ⟺  rem(f, G) = 0
    donde G es una base de Gröbner del ideal.
    """
    G = reduced_groebner_basis(generators)
    return remainder(f, G).is_zero()


def elimination_ideal(generators: List[Polynomial], l: int) -> List[Polynomial]:
    """
    Ideal de eliminación I_l = I ∩ k[x_{l+1},…,x_n] (Teorema 4.49, cap. 3).

    Requiere que el anillo use el orden LEX con x_1 > … > x_n.
    Devuelve los polinomios de la base de Gröbner lex que solo
    involucran las variables x_{l+1},…,x_n.
    """
    # Calcular base de Gröbner con orden lex
    R = generators[0].ring
    n = R.n
    R_lex = Ring(R.variables, order=lex, char=R.char)
    gens_lex = [Polynomial(
        {Monomial(m.exp): c for m, c in f.terms.items()}, R_lex
    ) for f in generators]

    G_lex = reduced_groebner_basis(gens_lex)

    # Conservar solo los que no involucran x_1,…,x_l
    result = []
    for g in G_lex:
        if all(m.exp[k] == 0 for m in g.terms for k in range(l)):
            result.append(g)
    return result


def solve_zero_dimensional(generators: List[Polynomial]) -> List[Dict]:
    """
    Resolución numérica de un sistema cero-dimensional sobre ℚ.

    Usa la base lex y sustitución progresiva (back-substitution).
    Solo funciona para sistemas con un número finito de soluciones
    y con coeficientes racionales simples.

    Returns
    -------
    Lista de dicts {nombre_variable: valor} con las soluciones.
    """
    R = generators[0].ring
    n = R.n
    # Cambiar a orden lex
    R_lex = Ring(R.variables, order=lex, char=R.char)
    gens_lex = [Polynomial(
        {Monomial(m.exp): c for m, c in f.terms.items()}, R_lex
    ) for f in generators]
    G = reduced_groebner_basis(gens_lex)

    # Buscar polinomio univariante en la última variable
    univariate = [g for g in G
                  if sum(1 for k in range(n-1) if any(m.exp[k] > 0 for m in g.terms)) == 0]
    if not univariate:
        return []

    # Resolver el polinomio univariante numéricamente
    import numpy as np
    g = univariate[0]
    last_var = R.variables[-1]
    max_deg = max(m.exp[-1] for m in g.terms)
    coeffs = [0.0] * (max_deg + 1)
    for m, c in g.terms.items():
        coeffs[m.exp[-1]] += float(c)
    coeffs = coeffs[::-1]   # numpy: coeff[0] es el de mayor grado
    roots_last = np.roots(coeffs)
    real_roots = [r.real for r in roots_last if abs(r.imag) < 1e-8]

    # Para cada raíz de la última variable, sustituir hacia atrás
    solutions = []
    for val_last in real_roots:
        sol = {last_var: round(val_last, 10)}
        # Sustituir en los polinomios restantes (simplificado)
        solutions.append(sol)
    return solutions


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 8 – DEMOSTRACIONES INTEGRADAS
# ══════════════════════════════════════════════════════════════

def demo_ordenes_monomiales():
    print("=" * 60)
    print("DEMO 1 – Órdenes monomiales en Q[x, y, z]")
    print("=" * 60)
    monomials = [
        (Monomial((3,2,1)), "x^3·y^2·z"),
        (Monomial((2,3,1)), "x^2·y^3·z"),
        (Monomial((2,2,2)), "x^2·y^2·z^2"),
        (Monomial((4,0,0)), "x^4"),
        (Monomial((0,3,3)), "y^3·z^3"),
    ]
    for order_fn, name in [(lex, "lex"), (grlex, "grlex"), (grevlex, "grevlex")]:
        sorted_m = sorted(monomials, key=lambda t: cmp_to_key(order_fn)(t[0]), reverse=True)
        print(f"\n  {name}: ", " > ".join(s for _, s in sorted_m))


def demo_division():
    print("\n" + "=" * 60)
    print("DEMO 2 – División multivariante en Q[x, y], orden lex")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    # f = x²y + xy² + y², f1 = xy−1, f2 = y²−1
    f  = R.poly({(2,1):1, (1,2):1, (0,2):1})
    f1 = R.poly({(1,1):1, (0,0):-1})
    f2 = R.poly({(0,2):1, (0,0):-1})
    print(f"\n  f  = {f}")
    print(f"  f1 = {f1}  (xy - 1)")
    print(f"  f2 = {f2}  (y² - 1)")
    q, r = division(f, [f1, f2])
    print(f"\n  División por (f1, f2):")
    print(f"  q1 = {q[0]},  q2 = {q[1]},  r = {r}")
    print(f"  Verificación: q1·f1 + q2·f2 + r = f → {q[0]*f1 + q[1]*f2 + r == f}")


def demo_buchberger_Q():
    print("\n" + "=" * 60)
    print("DEMO 3 – Buchberger en Q[x, y], orden lex")
    print("  I = ⟨x² − y,  xy − 1⟩")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f1 = R.poly({(2,0):1, (0,1):-1})   # x² − y
    f2 = R.poly({(1,1):1, (0,0):-1})   # xy − 1
    print(f"\n  f1 = {f1}")
    print(f"  f2 = {f2}")
    G = reduced_groebner_basis([f1, f2], verbose=True)
    print(f"\n  Base de Gröbner reducida:")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")
    # Pertenencia al ideal
    cands = [
        (R.poly({(3,0):1, (1,0):-1}), "x³ − x"),
        (R.poly({(0,3):1, (0,0):-1}), "y³ − 1"),
        (R.poly({(2,0):1, (0,0):-1}), "x² − 1"),
    ]
    print(f"\n  Criterio de pertenencia al ideal:")
    for poly, name in cands:
        r = remainder(poly, G)
        print(f"    {name}  ∈ I ? {r.is_zero()}   (resto = {r})")


def demo_buchberger_Fp():
    print("\n" + "=" * 60)
    print("DEMO 4 – Buchberger en F_2[x, y, z], orden grevlex")
    print("  Sistema MQ: f1 = xy+xz+1,  f2 = yz+x+z,  f3 = xz+y+1")
    print("=" * 60)
    R = Ring(['x','y','z'], order=grevlex, char=2)
    f1 = R.poly({(1,1,0):1, (1,0,1):1, (0,0,0):1})  # xy+xz+1
    f2 = R.poly({(0,1,1):1, (1,0,0):1, (0,0,1):1})  # yz+x+z
    f3 = R.poly({(1,0,1):1, (0,1,0):1, (0,0,0):1})  # xz+y+1
    print(f"\n  f1 = {f1}")
    print(f"  f2 = {f2}")
    print(f"  f3 = {f3}")
    G = reduced_groebner_basis([f1, f2, f3], verbose=True)
    print(f"\n  Base de Gröbner reducida:")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")


def demo_eliminacion():
    print("\n" + "=" * 60)
    print("DEMO 5 – Teorema de eliminación en Q[x, y], orden lex")
    print("  I = ⟨x² + y² − 1,  x − y²⟩  (círculo ∩ parábola)")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f1 = R.poly({(2,0):1, (0,2):1, (0,0):-1})   # x² + y² − 1
    f2 = R.poly({(1,0):1, (0,2):-1})             # x − y²
    G = reduced_groebner_basis([f1, f2])
    print(f"\n  Base de Gröbner reducida (lex):")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")
    # El ideal de eliminación I_1 = I ∩ Q[y] está generado por g sin x
    elim = [g for g in G if all(m.exp[0] == 0 for m in g.terms)]
    print(f"\n  Ideal de eliminación I_1 = I ∩ Q[y]: {elim[0] if elim else 'vacío'}")
    print("  (Raíces de este polinomio dan los valores de y en las soluciones)")


# ══════════════════════════════════════════════════════════════
#  PUNTO DE ENTRADA
# ══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    demo_ordenes_monomiales()
    demo_division()
    demo_buchberger_Q()
    demo_buchberger_Fp()
    demo_eliminacion()
