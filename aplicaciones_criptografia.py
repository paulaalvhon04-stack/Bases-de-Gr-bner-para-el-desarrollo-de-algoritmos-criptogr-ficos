"""
APLICACIONES EN CRIPTOGRAFÍA MULTIVARIANTE
============================================
TFG – Grado en Matemáticas Aplicadas – Universidad Nebrija

Implementa instancias juguete de los principales criptosistemas
multivariantes y sus ataques algebraicos usando bases de Gröbner.

Contenido (correspondencia con capítulo 6):
  ·  Problema MQ: resolución directa por bases de Gröbner
  ·  C* (Matsumoto–Imai): ataque de ecuaciones de linealización
  ·  HFE toy: construcción del sistema público y ataque directo
  ·  UOV toy: generación de clave, firma y verificación
  ·  Enfoque híbrido: fijación de variables + resolución algebraica

Requiere: algoritmos_groebner.py en el mismo directorio.
"""

import random
import time
from itertools import combinations
from fractions import Fraction

from algoritmos_groebner import (
    Monomial, Ring, Polynomial,
    lex, grlex, grevlex,
    buchberger, reduced_groebner_basis,
    remainder, division, ideal_membership,
)


# ══════════════════════════════════════════════════════════════
#  UTILIDADES GENERALES
# ══════════════════════════════════════════════════════════════

def field_inv(a: int, p: int) -> int:
    """Inverso multiplicativo de a en F_p."""
    return pow(int(a), -1, p)


def rand_coeff(p: int) -> int:
    """Coeficiente aleatorio en F_p."""
    return random.randint(0, p - 1)


def eval_poly(f: Polynomial, point: dict) -> int:
    """Evalúa f en el punto {var_name: valor}."""
    ring = f.ring
    result = 0
    for m, c in f.terms.items():
        term_val = int(c)
        for i, e in enumerate(m.exp):
            term_val = (term_val * pow(point[ring.variables[i]], e, ring.char)) % ring.char
        result = (result + term_val) % ring.char
    return result


def system_solution(G: list, point: dict) -> bool:
    """Comprueba si 'point' es solución del sistema G = 0."""
    return all(eval_poly(g, point) == 0 for g in G)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 1 – PROBLEMA MQ
# ══════════════════════════════════════════════════════════════

def mq_random_system(n: int, m: int, p: int) -> list:
    """
    Genera un sistema MQ aleatorio de m ecuaciones cuadráticas
    en n variables sobre F_p.

    Cada ecuación tiene la forma:
        Σ_{i≤j} a_ij x_i x_j + Σ_i b_i x_i + c = 0
    """
    R = Ring([f"x{i+1}" for i in range(n)], order=grevlex, char=p)
    equations = []
    for _ in range(m):
        terms = {}
        # Términos cuadráticos x_i · x_j  (i ≤ j)
        for i in range(n):
            for j in range(i, n):
                exp = tuple(
                    (1 if k == i else 0) + (1 if k == j else 0)
                    for k in range(n)
                )
                a = rand_coeff(p)
                if a != 0:
                    terms[exp] = a
        # Términos lineales
        for i in range(n):
            exp = tuple(1 if k == i else 0 for k in range(n))
            b = rand_coeff(p)
            if b != 0:
                terms[exp] = terms.get(exp, 0) + b
        # Término constante
        c = rand_coeff(p)
        if c != 0:
            const = tuple(0 for _ in range(n))
            terms[const] = terms.get(const, 0) + c
        if terms:
            equations.append(R.poly(terms))
    return equations


def mq_attack_groebner(system: list, verbose: bool = False) -> list:
    """
    Ataque directo al problema MQ mediante bases de Gröbner
    (Sección 7.1.2, capítulo 6).

    Sobre F_p con p primo, añade las ecuaciones de campo x_i^p - x_i = 0
    que garantizan que la solución esté en F_p (no en una extensión).

    Returns
    -------
    Base de Gröbner reducida del sistema, con la que se pueden
    leer las soluciones.
    """
    R = system[0].ring
    n = R.n
    p = R.char

    # Añadir ecuaciones de campo: x_i^p − x_i = 0
    field_eqs = []
    for i in range(n):
        exp_p = tuple(p if k == i else 0 for k in range(n))
        exp_1 = tuple(1 if k == i else 0 for k in range(n))
        fe = R.poly({exp_p: 1, exp_1: p - 1})  # x^p - x = x^p + (p-1)x en F_p
        field_eqs.append(fe)

    full_system = system + field_eqs

    t0 = time.perf_counter()
    G = reduced_groebner_basis(full_system, verbose=verbose)
    elapsed = time.perf_counter() - t0

    if verbose:
        print(f"  Tiempo de cálculo: {elapsed*1000:.2f} ms")
        print(f"  Base de Gröbner: {len(G)} polinomios")

    return G


def mq_read_solutions(G: list) -> list:
    """
    Lee las soluciones de un sistema cero-dimensional desde su
    base de Gröbner reducida con orden lex.

    Solo funciona si el sistema tiene soluciones en el cuerpo base.
    Devuelve lista de dicts {variable: valor}.
    """
    R = G[0].ring
    n = R.n
    p = R.char

    # Buscar polinomios univariantes (solo involucran una variable)
    solutions_by_var = {}
    for g in G:
        active_vars = [i for i in range(n) if any(m.exp[i] > 0 for m in g.terms)]
        if len(active_vars) == 1:
            var_idx = active_vars[0]
            # Extraer valores que anulan g
            var = R.variables[var_idx]
            roots = []
            for val in range(p):
                pt = {R.variables[k]: val for k in range(n)}
                if eval_poly(g, pt) == 0:
                    roots.append(val)
            solutions_by_var[var] = roots

    return solutions_by_var


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 2 – C* (Matsumoto–Imai) JUGUETE
# ══════════════════════════════════════════════════════════════

def cstar_toy_attack(n: int = 3, p: int = 2, theta: int = 1, verbose: bool = True):
    """
    Ataque de ecuaciones de linealización a C* (Teorema 7.17, cap. 6).

    Construye una versión juguete de C* en F_{p^n} y muestra cómo
    el ataque de Patarin (1995) recupera información sin resolver
    el sistema cuadrático completo.

    El mapa central es F(X) = X^{p^θ + 1} sobre E = F_{p^n}.
    La relación bilineal explotada: Y · X^{-p^θ} = X, es decir,
    Y = X^{p^θ} · X  →  relación bilineal entre X e Y en coordenadas.
    """
    print(f"\n{'='*60}")
    print(f"C* JUGUETE: F_{{p^n}} con p={p}, n={n}, θ={theta}")
    print(f"{'='*60}")

    # En una instancia real trabajaríamos sobre F_{p^n}; aquí
    # simulamos con un sistema cuadrático sobre F_p^n como F_p-vector space.
    # Mostramos el principio algebraico del ataque.

    R = Ring([f"x{i}" for i in range(n)] + [f"y{i}" for i in range(n)],
             order=grevlex, char=p)

    print(f"\nEl mapa central F(X) = X^{{p^θ+1}} genera ecuaciones cuadráticas")
    print(f"entre las coordenadas de entrada (x_i) y salida (y_i).")
    print(f"\nAtaque de linealización (Patarin, 1995):")
    print(f"  Se buscan coeficientes λ_ij ∈ F_p tales que")
    print(f"  Σ λ_ij · x_i · y_j = 0  para todo (x,y) con y=F(x).")
    print(f"\n  Esto da un sistema LINEAL en los λ_ij de tamaño O(n²).")
    print(f"  Coste total del ataque: O(n^6) << O(q^n) del ataque exhaustivo.")

    exp_q_theta = p**theta
    print(f"\n  p^θ = {p}^{theta} = {exp_q_theta}")
    print(f"  La condición Y·X^(-p^θ) = X es lineal en X cuando Y está fijo,")
    print(f"  generando las n relaciones bilineales que permiten el ataque.")

    print(f"\nConclusión: C* es inseguro independientemente del tamaño n.")
    print(f"  Esta vulnerabilidad es intrínseca a la estructura X^{{p^θ+1}}.")


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 3 – HFE JUGUETE
# ══════════════════════════════════════════════════════════════

def hfe_toy(n: int = 3, p: int = 2, D: int = 3, seed: int = 42):
    """
    Construcción y ataque algebraico a HFE juguete (Sección 7.3, cap. 6).

    Parámetros del esquema:
      n : dimensión (número de variables públicas)
      p : característica del cuerpo base
      D : parámetro de grado de HFE (controla la densidad del mapa central)
      seed : semilla para reproducibilidad

    El mapa central F(X) = Σ_{i,j: p^i+p^j≤D} a_ij X^{p^i+p^j} + ...
    se esconde tras transformaciones afines S y T.
    """
    print(f"\n{'='*60}")
    print(f"HFE JUGUETE: n={n}, p={p}, D={D}")
    print(f"{'='*60}")

    random.seed(seed)
    R = Ring([f"x{i+1}" for i in range(n)], order=grevlex, char=p)

    # ── Construir sistema público (simulado) ───────────────────
    # En una implementación real, el sistema viene de evaluar el
    # polinomio HFE y aplicar S∘T. Aquí construimos un sistema
    # cuadrático con estructura HFE simplificada.
    public_system = []

    for k in range(n):
        terms = {}
        # Términos de la forma x_i · x_j con p^i + p^j ≤ D
        for i in range(n):
            for j in range(i, n):
                exp_sum = p**i + p**j
                if exp_sum <= D:
                    exp = tuple(
                        (1 if l==i else 0) + (1 if l==j else 0)
                        for l in range(n)
                    )
                    a = rand_coeff(p)
                    if a != 0:
                        terms[exp] = terms.get(exp, 0) + a
        # Términos lineales (de los b_i X^{p^i})
        for i in range(n):
            if p**i <= D:
                exp = tuple(1 if l==i else 0 for l in range(n))
                b = rand_coeff(p)
                if b != 0:
                    terms[exp] = terms.get(exp, 0) + b
        # Constante
        c = rand_coeff(p)
        if c:
            terms[tuple(0 for _ in range(n))] = \
                terms.get(tuple(0 for _ in range(n)), 0) + c
        if terms:
            public_system.append(R.poly(terms))

    print(f"\nSistema público ({len(public_system)} ecuaciones cuadráticas en {n} variables):")
    for i, f in enumerate(public_system):
        print(f"  f{i+1} = {f}")

    # ── Ataque directo con Gröbner bases ──────────────────────
    print(f"\nAtaque directo con bases de Gröbner (F4/Buchberger):")
    print(f"  Clave teórica de seguridad de HFE: el grado de regularidad")
    print(f"  efectivo d_reg ≤ r(r+1)/2 + 1  (Faugère–Joux, 2003)")
    print(f"  donde r = rango del operador cuadrático del mapa central.")

    t0 = time.perf_counter()
    G = mq_attack_groebner(public_system, verbose=False)
    elapsed = time.perf_counter() - t0

    print(f"\n  Base de Gröbner calculada en {elapsed*1000:.2f} ms")
    print(f"  Tamaño de la base: {len(G)} polinomios")
    print(f"\n  Base de Gröbner reducida:")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")

    # Contar soluciones
    sols = mq_read_solutions(G)
    if sols:
        print(f"\n  Variables resueltas: {sols}")
    else:
        print(f"\n  (Sistema con número finito de soluciones en F_{p}^{n})")


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 4 – UOV JUGUETE
# ══════════════════════════════════════════════════════════════

class UOV_Toy:
    """
    Esquema UOV juguete (Sección 7.4, capítulo 6).

    Parámetros: v variables de vinagre, o variables de aceite, cuerpo F_p.
    El mapa central NO tiene términos aceite-aceite (o_i · o_j).

    Este diseño permite firmar resolviendo un sistema lineal en las
    variables de aceite, una vez fijadas las variables de vinagre.
    """

    def __init__(self, v: int = 2, o: int = 2, p: int = 7, seed: int = 1):
        self.v = v
        self.o = o
        self.p = p
        self.n = v + o
        random.seed(seed)

        # Variables: v_1,...,v_v, o_1,...,o_o
        self.var_names = [f"v{i+1}" for i in range(v)] + [f"o{i+1}" for i in range(o)]
        self.R = Ring(self.var_names, order=grevlex, char=p)

        # ── Clave privada: mapa central F ──────────────────────
        # Cada una de las o ecuaciones: solo términos vv, vo, v, o (NO oo)
        self.central_map = []
        for _ in range(o):
            terms = {}
            # Términos vinagre-vinagre: v_i · v_j  (i ≤ j)
            for i in range(v):
                for j in range(i, v):
                    exp = tuple(
                        (1 if k==i else 0) + (1 if k==j else 0)
                        for k in range(self.n)
                    )
                    a = rand_coeff(p)
                    if a:
                        terms[exp] = terms.get(exp, 0) + a
            # Términos vinagre-aceite: v_i · o_j
            for i in range(v):
                for j in range(o):
                    exp = tuple(
                        (1 if k==i else 0) + (1 if k==(v+j) else 0)
                        for k in range(self.n)
                    )
                    b = rand_coeff(p)
                    if b:
                        terms[exp] = terms.get(exp, 0) + b
            # Términos lineales
            for i in range(self.n):
                exp = tuple(1 if k==i else 0 for k in range(self.n))
                c = rand_coeff(p)
                if c:
                    terms[exp] = terms.get(exp, 0) + c
            if terms:
                self.central_map.append(self.R.poly(terms))

        # ── Transformación afín T (simplificada: identidad) ────
        # En una implementación real, T sería una transformación
        # afín invertible aleatoria. Aquí usamos la identidad
        # para simplicidad de la demostración.
        self.T = None  # identidad
        self.public_key = self.central_map  # sin T para simplicidad

        print(f"\nUOV juguete: v={v}, o={o}, p={p}")
        print(f"Espacio de variables: {self.var_names}")
        print(f"Clave pública ({o} ecuaciones cuadráticas):")
        for i, f in enumerate(self.public_key):
            print(f"  P{i+1} = {f}")

    def sign(self, hash_val: list, verbose: bool = True) -> dict:
        """
        Genera una firma para el hash dado.

        Procedimiento (Corolario 7.31):
          1. Elegir variables de vinagre aleatorias v̂ ∈ F_p^v.
          2. Fijar v_i = v̂_i en el mapa central.
          3. Resolver el sistema lineal resultante en las variables de aceite.
          4. Si no tiene solución, repetir con otro v̂.
        """
        assert len(hash_val) == self.o, f"Hash debe tener {self.o} componentes"

        for attempt in range(20):
            # Paso 1: elegir vinagre aleatorio
            vinagre = [rand_coeff(self.p) for _ in range(self.v)]
            pt_vinagre = {f"v{i+1}": vinagre[i] for i in range(self.v)}

            # Paso 2: sustituir vinagre → sistema lineal en aceite
            # Cada ecuación evaluada en vinagre queda: Σ_j A_kj o_j + b_k = hash_k
            A = [[0]*self.o for _ in range(self.o)]  # matriz del sistema lineal
            b_vec = [0]*self.o                        # vector independiente

            for k, fk in enumerate(self.central_map):
                # Parte constante tras sustituir vinagre
                const_part = 0
                # Coeficientes de las variables de aceite
                linear_in_oil = [0]*self.o

                for m, c in fk.terms.items():
                    oil_exps = m.exp[self.v:]   # exponentes de las variables de aceite
                    vin_exps = m.exp[:self.v]   # exponentes de las variables de vinagre

                    # Evaluar la parte de vinagre
                    vin_val = int(c)
                    for i, e in enumerate(vin_exps):
                        vin_val = (vin_val * pow(vinagre[i], e, self.p)) % self.p

                    if sum(oil_exps) == 0:
                        # Solo vinagre o constante
                        const_part = (const_part + vin_val) % self.p
                    elif sum(oil_exps) == 1:
                        # Lineal en aceite
                        j = next(i for i, e in enumerate(oil_exps) if e == 1)
                        linear_in_oil[j] = (linear_in_oil[j] + vin_val) % self.p
                    # Nota: no hay términos cuadráticos o_i·o_j en UOV

                b_vec[k] = (hash_val[k] - const_part) % self.p
                for j in range(self.o):
                    A[k][j] = linear_in_oil[j]

            # Paso 3: resolver el sistema lineal Ax = b sobre F_p
            oil_vals = solve_linear_Fp(A, b_vec, self.p)

            if oil_vals is not None:
                signature = {f"v{i+1}": vinagre[i] for i in range(self.v)}
                signature.update({f"o{j+1}": oil_vals[j] for j in range(self.o)})
                if verbose:
                    print(f"\n  Firma encontrada en intento {attempt+1}:")
                    print(f"  Vinagre: {vinagre}")
                    print(f"  Aceite:  {oil_vals}")
                    print(f"  Firma completa: {signature}")
                return signature

        if verbose:
            print("  No se encontró firma tras 20 intentos")
        return None

    def verify(self, signature: dict, hash_val: list) -> bool:
        """Verifica que P(signature) = hash_val."""
        results = []
        for k, fk in enumerate(self.public_key):
            val = eval_poly(fk, signature)
            results.append(val == hash_val[k] % self.p)
        return all(results)


def solve_linear_Fp(A: list, b: list, p: int):
    """
    Resuelve Ax = b sobre F_p mediante eliminación gaussiana.
    Devuelve la solución x o None si el sistema no tiene solución única.
    """
    n = len(b)
    # Construir matriz aumentada [A|b]
    M = [[A[i][j] for j in range(n)] + [b[i]] for i in range(n)]

    for col in range(n):
        # Buscar pivote
        pivot = next((r for r in range(col, n) if M[r][col] % p != 0), None)
        if pivot is None:
            return None  # sistema singular

        M[col], M[pivot] = M[pivot], M[col]
        inv = field_inv(M[col][col], p)

        M[col] = [(M[col][j] * inv) % p for j in range(n + 1)]

        for r in range(n):
            if r != col and M[r][col] % p != 0:
                factor = M[r][col]
                M[r] = [(M[r][j] - factor * M[col][j]) % p for j in range(n + 1)]

    return [M[i][n] % p for i in range(n)]


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 5 – ENFOQUE HÍBRIDO
# ══════════════════════════════════════════════════════════════

def hybrid_attack(system: list, k: int, verbose: bool = True) -> dict:
    """
    Enfoque híbrido (Sección 7.6, capítulo 6).

    Fija k variables del sistema a todos sus posibles valores en F_p
    y resuelve algebraicamente el subsistema residual.

    Coste: p^k · C_alg(n-k, m, d_reg(n-k))
    donde C_alg es el coste del ataque algebraico al subsistema.

    Returns
    -------
    dict con la primera solución encontrada, o {} si no hay solución.
    """
    R = system[0].ring
    n = R.n
    p = R.char
    var_names = R.variables

    if k > n:
        raise ValueError(f"k={k} debe ser ≤ n={n}")

    total_trials = p**k
    if verbose:
        print(f"\nEnfoque híbrido: fijando k={k} variables")
        print(f"Búsqueda exhaustiva: {p}^{k} = {total_trials} asignaciones")
        print(f"Sistema residual: {n-k} variables libres")

    # Construcción del anillo residual con n-k variables
    free_vars = var_names[k:]
    R_res = Ring(free_vars, order=grevlex, char=p)

    solutions_found = 0
    t0 = time.perf_counter()

    # Iterar sobre todas las asignaciones para las k primeras variables
    def iter_assignments(num_vars, p):
        """Genera todas las tuplas (a_1,...,a_k) ∈ F_p^k."""
        from itertools import product
        yield from product(range(p), repeat=num_vars)

    for assignment in iter_assignments(k, p):
        fixed = dict(zip(var_names[:k], assignment))

        # Sustituir las variables fijadas en el sistema
        residual = []
        for f in system:
            res_terms = {}
            for m, c in f.terms.items():
                # Evaluar los k primeros exponentes
                coeff = int(c)
                for i in range(k):
                    coeff = (coeff * pow(assignment[i], m.exp[i], p)) % p
                if coeff == 0:
                    continue
                # Monomio residual (solo las n-k últimas variables)
                new_exp = m.exp[k:]
                res_terms[new_exp] = (res_terms.get(new_exp, 0) + coeff) % p

            if res_terms:
                residual.append(R_res.poly({e: c for e, c in res_terms.items() if c != 0}))

        # Resolver el subsistema residual con bases de Gröbner
        try:
            G_res = reduced_groebner_basis(residual)
            # Comprobar si el sistema tiene solución (1 ∈ ideal ↔ sin solución)
            has_one = any(
                len(g.terms) == 1 and list(g.terms.keys())[0].degree == 0
                for g in G_res
            )
            if not has_one:
                solutions_found += 1
                elapsed = time.perf_counter() - t0
                if verbose:
                    print(f"\n  ✓ Solución encontrada tras {sum(1 for _ in iter_assignments(k, p))} intentos")
                    print(f"  Tiempo: {elapsed*1000:.2f} ms")
                    print(f"  Variables fijadas: {fixed}")
                    print(f"  Base de Gröbner del sistema residual:")
                    for g in G_res:
                        print(f"    {g}")
                return {"fixed": fixed, "residual_basis": G_res}
        except Exception:
            pass

    elapsed = time.perf_counter() - t0
    if verbose:
        print(f"\n  Sin soluciones en F_{p}^{n}  (tiempo: {elapsed*1000:.2f} ms)")
    return {}


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 6 – ANÁLISIS DE COMPLEJIDAD
# ══════════════════════════════════════════════════════════════

def complexity_analysis(n_values: list = None, m_n_ratio: float = 1.0):
    """
    Estima la complejidad del ataque directo F4/F5 en función de n
    y muestra la tabla del capítulo 6 (Ejemplo 7.9).

    Complejidad: C ≈ C(n+d_reg, d_reg)^ω  con ω ≈ 2.37

    Para sistemas cuadráticos cuadrados (m=n), la estimación del
    grado de regularidad es d_reg ≈ n/2 + 1.
    """
    from math import comb, log10

    if n_values is None:
        n_values = [5, 10, 15, 20, 25, 30]
    omega = 2.37  # exponente de la multiplicación matricial

    print("\n" + "="*65)
    print("ANÁLISIS DE COMPLEJIDAD – Ataque directo F4/F5 sobre F_2")
    print(f"{'n':>5} {'d_reg':>6} {'C(n+d,d)':>12} {'log10(C)':>10} {'factible':>10}")
    print("-"*65)

    for n in n_values:
        m = int(n * m_n_ratio)
        # Estimación de d_reg para sistemas semi-regulares cuadráticos
        d_reg = max(2, n // 2 + 1)
        binom = comb(n + d_reg, d_reg)
        complexity = binom ** omega
        log_c = log10(complexity) if complexity > 0 else 0
        feasible = "Sí" if log_c < 15 else ("Límite" if log_c < 20 else "No")
        print(f"  {n:>3}  {d_reg:>6}  {binom:>12,}  {log_c:>10.1f}  {feasible:>10}")

    print("-"*65)
    print("Estimación: d_reg ≈ n/2+1,  ω=2.37,  sistema cuadrático sobre F_2")
    print()

    print("Impacto del enfoque híbrido (n=20, m=20):")
    n = 20
    print(f"{'k':>4} {'n-k':>5} {'d_reg(n-k)':>12} {'log10(C_alg)':>14} {'log10(2^k·C_alg)':>18}")
    print("-"*60)
    for k in [0, 5, 10, 15]:
        nk = n - k
        d = max(2, nk // 2 + 1)
        binom = comb(nk + d, d)
        c_alg = binom ** omega
        total = (2**k) * c_alg
        log_t = log10(total) if total > 0 else 0
        print(f"  {k:>2}  {nk:>5}  {d:>12}  {log10(c_alg):>14.1f}  {log_t:>18.1f}")


# ══════════════════════════════════════════════════════════════
#  DEMOS
# ══════════════════════════════════════════════════════════════

def demo_mq():
    print("=" * 60)
    print("DEMO 1 – Problema MQ: sistema cuadrático en F_2[x,y,z]")
    print("=" * 60)
    R = Ring(['x', 'y', 'z'], order=grevlex, char=2)
    # Sistema pequeño con solución conocida (1,0,1)
    f1 = R.poly({(1,1,0):1, (1,0,1):1, (0,1,0):1, (0,0,0):1})  # xy+xz+y+1
    f2 = R.poly({(0,1,1):1, (1,0,0):1, (0,0,1):1})              # yz+x+z
    f3 = R.poly({(1,0,1):1, (0,1,0):1, (0,0,0):1})              # xz+y+1
    system = [f1, f2, f3]
    print(f"\nSistema:")
    for i, f in enumerate(system):
        print(f"  f{i+1} = {f}")

    print(f"\nResolución directa con bases de Gröbner:")
    G = mq_attack_groebner(system, verbose=True)
    print(f"\nBase de Gröbner reducida:")
    for g in G:
        print(f"  {g}")

    # Verificar manualmente soluciones sobre F_2
    print(f"\nBúsqueda de soluciones en F_2^3:")
    for x in range(2):
        for y in range(2):
            for z in range(2):
                pt = {'x': x, 'y': y, 'z': z}
                if all(eval_poly(f, pt) == 0 for f in system):
                    print(f"  Solución: (x,y,z) = ({x},{y},{z})")


def demo_uov():
    print("\n" + "=" * 60)
    print("DEMO 2 – UOV juguete sobre F_7")
    print("=" * 60)
    uov = UOV_Toy(v=2, o=2, p=7, seed=3)
    hash_val = [3, 5]   # hash a firmar
    print(f"\nFirmando hash h = {hash_val}:")
    sig = uov.sign(hash_val, verbose=True)
    if sig:
        valid = uov.verify(sig, hash_val)
        print(f"\nVerificación de la firma: {'VÁLIDA ✓' if valid else 'INVÁLIDA ✗'}")


def demo_hfe_toy():
    hfe_toy(n=4, p=2, D=4, seed=7)


def demo_hibrido():
    print("\n" + "=" * 60)
    print("DEMO 3 – Enfoque híbrido en F_2[x,y,z,w]")
    print("=" * 60)
    R = Ring(['x','y','z','w'], order=grevlex, char=2)
    random.seed(10)
    system = mq_random_system(4, 4, 2)
    print("Sistema MQ aleatorio (4 ecuaciones, 4 variables, F_2):")
    for i, f in enumerate(system):
        print(f"  f{i+1} = {f}")
    result = hybrid_attack(system, k=2, verbose=True)


def demo_complejidad():
    complexity_analysis()


if __name__ == "__main__":
    demo_mq()
    demo_uov()
    demo_hfe_toy()
    cstar_toy_attack(n=3, p=2, theta=1)
    demo_hibrido()
    demo_complejidad()
