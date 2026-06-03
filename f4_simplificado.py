"""
ALGORITMO F4 SIMPLIFICADO – MATRICES DE MACAULAY
==================================================
TFG – Grado en Matemáticas Aplicadas – Universidad Nebrija

Implementa una versión simplificada del algoritmo F4 (Faugère, 1999).

Idea clave (capítulo 5): en lugar de reducir un S-polinomio cada vez,
F4 agrupa TODOS los S-polinomios de un mismo grado en una matriz de
Macaulay y los reduce simultáneamente mediante eliminación gaussiana.

Requiere: algoritmos_groebner.py en el mismo directorio.
"""

import numpy as np
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations
from typing import List, Tuple, Dict, Optional
import time

from algoritmos_groebner import (
    Monomial, Ring, Polynomial, lex, grlex, grevlex,
    s_polynomial, division, remainder,
    reduced_groebner_basis as buchberger_reduced,
)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 1 – UTILIDADES PARA LA MATRIZ DE MACAULAY
# ══════════════════════════════════════════════════════════════

def all_monomials_up_to_degree(n: int, d: int) -> List[Monomial]:
    """
    Genera todos los monomios de grado total ≤ d en n variables.

    Número de monomios: C(n+d, d).
    Los ordena de mayor a menor con grlex para usar como columnas
    de la matriz de Macaulay.
    """
    result = []

    def gen(exp, remaining_vars, remaining_degree):
        if remaining_vars == 0:
            result.append(Monomial(exp))
            return
        for e in range(remaining_degree + 1):
            gen(exp + [e], remaining_vars - 1, remaining_degree - e)

    gen([], n, d)
    # Ordenar de mayor a menor con grlex
    result.sort(key=cmp_to_key(grlex), reverse=True)
    return result


def poly_to_row(f: Polynomial, col_index: Dict[Monomial, int]) -> np.ndarray:
    """
    Convierte un polinomio en un vector fila (para la matriz de Macaulay).

    col_index : dict {Monomial: índice_columna}
    """
    row = np.zeros(len(col_index), dtype=float)
    for m, c in f.terms.items():
        if m in col_index:
            row[col_index[m]] = float(c)
    return row


def row_to_poly(row: np.ndarray, col_monomials: List[Monomial], ring: Ring, tol=1e-9) -> Polynomial:
    """
    Convierte una fila de la matriz de Macaulay en un polinomio.
    """
    terms = {}
    for j, m in enumerate(col_monomials):
        c = row[j]
        if abs(c) > tol:
            if ring.char == 0:
                terms[m] = Fraction(c).limit_denominator(10**9)
            else:
                terms[m] = int(round(c)) % ring.char
    return Polynomial(terms, ring)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 2 – CONSTRUCCIÓN DE LA MATRIZ DE MACAULAY
# ══════════════════════════════════════════════════════════════

def build_macaulay_matrix(polys: List[Polynomial], degree: int) -> Tuple:
    """
    Construye la matriz de Macaulay de grado d (Definición 6.5, capítulo 5).

    Incluye todos los múltiplos monomiales de cada polinomio f_i
    de la forma x^α · f_i donde deg(x^α · f_i) ≤ d.

    Returns
    -------
    (matrix, col_monomials, ring)
      matrix        : np.ndarray de forma (num_filas, num_cols)
      col_monomials : lista de monomios (índice → monomio)
      ring          : el anillo de polinomios
    """
    if not polys:
        return np.zeros((0, 0)), [], polys[0].ring if polys else None

    ring = polys[0].ring
    n = ring.n

    # Columnas: todos los monomios de grado ≤ d
    col_monomials = all_monomials_up_to_degree(n, degree)
    col_index = {m: j for j, m in enumerate(col_monomials)}

    # Filas: x^α · f_i para cada f_i y cada monomio x^α
    rows = []
    for f in polys:
        if f.is_zero():
            continue
        lm_f = f.LM()
        deg_f = lm_f.degree

        # Generar todos los monomios x^α con deg(f) + deg(α) ≤ d
        possible_alphas = all_monomials_up_to_degree(n, degree - deg_f)
        for alpha in possible_alphas:
            # Calcular alpha · f
            scaled = {}
            for m, c in f.terms.items():
                new_m = m * alpha
                if new_m.degree <= degree:
                    scaled[new_m] = c
            if scaled:
                g = Polynomial(scaled, ring)
                row = poly_to_row(g, col_index)
                rows.append(row)

    if not rows:
        return np.zeros((0, len(col_monomials))), col_monomials, ring

    matrix = np.array(rows, dtype=float)
    return matrix, col_monomials, ring


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 3 – ELIMINACIÓN GAUSSIANA
# ══════════════════════════════════════════════════════════════

def gaussian_elimination(matrix: np.ndarray, char: int = 0, tol: float = 1e-9) -> np.ndarray:
    """
    Eliminación gaussiana por filas para obtener la forma escalonada
    reducida (rref). Esta es la operación central de F4.

    Sobre ℚ (char=0): aritmética de punto flotante con tolerancia tol.
    Sobre 𝔽_p (char=p): aritmética modular exacta.
    """
    M = matrix.copy()
    rows, cols = M.shape
    pivot_row = 0

    for col in range(cols):
        # Encontrar fila pivote (la de mayor valor absoluto en esta columna)
        col_vals = np.abs(M[pivot_row:, col])
        max_idx = np.argmax(col_vals) + pivot_row

        if M[max_idx, col] < tol:
            continue   # columna entera casi cero, pasar a la siguiente

        # Intercambiar filas
        M[[pivot_row, max_idx]] = M[[max_idx, pivot_row]]

        # Normalizar fila pivote
        M[pivot_row] = M[pivot_row] / M[pivot_row, col]

        # Eliminar en todas las demás filas (no solo las inferiores)
        for r in range(rows):
            if r != pivot_row and abs(M[r, col]) > tol:
                M[r] -= M[r, col] * M[pivot_row]

        pivot_row += 1
        if pivot_row >= rows:
            break

    # Limpiar valores casi nulos
    M[np.abs(M) < tol] = 0.0
    return M


def gaussian_elimination_Fp(matrix: np.ndarray, p: int) -> np.ndarray:
    """
    Eliminación gaussiana exacta sobre 𝔽_p.
    Las entradas se tratan como enteros mod p.
    """
    M = matrix.astype(int) % p
    rows, cols = M.shape
    pivot_row = 0

    for col in range(cols):
        # Buscar fila pivote no nula
        pivot_found = -1
        for r in range(pivot_row, rows):
            if M[r, col] % p != 0:
                pivot_found = r
                break
        if pivot_found < 0:
            continue

        # Intercambiar
        M[[pivot_row, pivot_found]] = M[[pivot_found, pivot_row]]

        # Normalizar: multiplicar por el inverso del pivote
        inv_pivot = pow(int(M[pivot_row, col]), -1, p)
        M[pivot_row] = (M[pivot_row] * inv_pivot) % p

        # Eliminar en todas las demás filas
        for r in range(rows):
            if r != pivot_row and M[r, col] % p != 0:
                factor = int(M[r, col])
                M[r] = (M[r] - factor * M[pivot_row]) % p

        pivot_row += 1
        if pivot_row >= rows:
            break

    return M % p


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 4 – ALGORITMO F4 SIMPLIFICADO
# ══════════════════════════════════════════════════════════════

def f4(generators: List[Polynomial], max_degree: Optional[int] = None,
       verbose: bool = False) -> List[Polynomial]:
    """
    Algoritmo F4 simplificado (Teorema 6.14, capítulo 5).

    Diferencia clave con Buchberger:
      · Buchberger: reduce un S-polinomio por vez.
      · F4: agrupa todos los S-polinomios del mismo grado mínimo
            en una matriz de Macaulay y los reduce todos a la vez
            mediante eliminación gaussiana.

    Esto permite reutilizar el trabajo lineal entre reducciones del
    mismo grado, y explotar implementaciones eficientes de BLAS/LAPACK.

    Parameters
    ----------
    generators  : lista de polinomios generadores
    max_degree  : grado máximo a procesar (None = automático)
    verbose     : imprime el estado en cada iteración de grado

    Returns
    -------
    G : lista de polinomios (base de Gröbner)
    """
    ring = generators[0].ring
    G = list(generators)
    P = list(combinations(range(len(G)), 2))   # pares pendientes

    if max_degree is None:
        # Heurística: doblar el grado máximo de los generadores
        max_degree = 2 * max(g.LM().degree for g in G if not g.is_zero())
        max_degree = max(max_degree, 4)

    if verbose:
        print(f"F4: inicio con {len(G)} generadores, max_degree={max_degree}")

    while P:
        # ── Paso 1: Selección – elegir todos los pares de grado mínimo ──
        min_deg = min(G[i].LM().lcm(G[j].LM()).degree for i, j in P)
        current_pairs = [(i, j) for i, j in P if G[i].LM().lcm(G[j].LM()).degree == min_deg]
        P = [(i, j) for i, j in P if (i, j) not in current_pairs]

        if min_deg > max_degree:
            if verbose:
                print(f"  Grado {min_deg} > max_degree={max_degree}, terminando")
            break

        if verbose:
            print(f"\n  Procesando {len(current_pairs)} pares de grado {min_deg}")

        # ── Paso 2: Construir S-polinomios de este grado ─────────────
        s_polys = []
        for i, j in current_pairs:
            sp = s_polynomial(G[i], G[j])
            if not sp.is_zero():
                s_polys.append(sp)

        if not s_polys:
            continue

        # ── Paso 3: Preprocesado simbólico + matriz de Macaulay ──────
        # Incluir los S-polinomios y todos los reductores necesarios
        polys_for_matrix = list(s_polys) + G
        matrix, col_monomials, _ = build_macaulay_matrix(polys_for_matrix, min_deg)

        if matrix.size == 0:
            continue

        if verbose:
            print(f"  Matriz de Macaulay: {matrix.shape[0]} filas × {matrix.shape[1]} cols")

        # ── Paso 4: Reducción matricial (eliminación gaussiana) ───────
        if ring.char == 0:
            reduced_matrix = gaussian_elimination(matrix)
        else:
            M_int = matrix.astype(int) % ring.char
            reduced_matrix = gaussian_elimination_Fp(M_int, ring.char)

        # ── Paso 5: Extraer polinomios nuevos ─────────────────────────
        # Son las filas no nulas cuyo término líder no está en ⟨LT(G)⟩
        current_lm_set = {g.LM() for g in G}
        new_polys_added = 0

        for row in reduced_matrix:
            p = row_to_poly(row, col_monomials, ring)
            if p.is_zero():
                continue
            lm_p = p.LM()
            # ¿El término líder es nuevo?
            if not any(lm_p.divisible_by(lm) for lm in current_lm_set):
                new_idx = len(G)
                G.append(p)
                P += [(k, new_idx) for k in range(new_idx)]
                current_lm_set.add(lm_p)
                new_polys_added += 1
                if verbose:
                    print(f"    + nuevo generador: {p}")

        if verbose:
            print(f"  → {new_polys_added} nuevos generadores añadidos")

    return G


def f4_reduced(generators: List[Polynomial], verbose: bool = False) -> List[Polynomial]:
    """Base de Gröbner reducida calculada con F4."""
    G_raw = f4(generators, verbose=verbose)
    # Reducir usando Buchberger (el paso de reducción es el mismo)
    return buchberger_reduced(G_raw)


# ══════════════════════════════════════════════════════════════
#  SECCIÓN 5 – COMPARACIÓN F4 vs BUCHBERGER
# ══════════════════════════════════════════════════════════════

def comparar_buchberger_f4(generators: List[Polynomial]):
    """
    Compara el resultado y el tiempo de ejecución de Buchberger y F4
    sobre el mismo conjunto de generadores.
    """
    print("\n" + "─" * 60)
    print("Comparación Buchberger vs F4")
    print("─" * 60)

    t0 = time.perf_counter()
    G_buch = buchberger_reduced(generators)
    t_buch = time.perf_counter() - t0

    t0 = time.perf_counter()
    G_f4 = f4_reduced(generators)
    t_f4 = time.perf_counter() - t0

    print(f"\nBuchberger: {len(G_buch)} generadores  ({t_buch*1000:.2f} ms)")
    for g in G_buch:
        print(f"  {g}")

    print(f"\nF4:         {len(G_f4)} generadores  ({t_f4*1000:.2f} ms)")
    for g in G_f4:
        print(f"  {g}")

    # Verificar que los términos líderes coinciden
    lm_buch = {g.LM() for g in G_buch}
    lm_f4   = {g.LM() for g in G_f4}
    print(f"\n¿Mismos términos líderes? {lm_buch == lm_f4}")


# ══════════════════════════════════════════════════════════════
#  DEMOS
# ══════════════════════════════════════════════════════════════

def demo_macaulay_matrix():
    print("=" * 60)
    print("DEMO – Matriz de Macaulay en grado 3")
    print("  Sistema: f1 = x²−y,  f2 = xy−1  en Q[x,y], lex")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f1 = R.poly({(2,0):1, (0,1):-1})
    f2 = R.poly({(1,1):1, (0,0):-1})

    matrix, col_monomials, _ = build_macaulay_matrix([f1, f2], degree=3)
    print(f"\nColumnas (monomios grado ≤ 3): {[str(m.exp) for m in col_monomials]}")
    print(f"Tamaño de la matriz: {matrix.shape[0]} filas × {matrix.shape[1]} cols")
    print("\nMatriz de Macaulay:")
    # Mostrar de forma legible
    header = "  " + "  ".join(f"({','.join(str(e) for e in m.exp)})" for m in col_monomials[:8])
    print(header)
    for i, row in enumerate(matrix[:8]):
        print(f"  fila {i+1}: {['%4.0f'%v for v in row[:8]]}")
    if matrix.shape[0] > 8:
        print(f"  ... ({matrix.shape[0]-8} filas más)")


def demo_f4_sistema_cuadratico():
    print("\n" + "=" * 60)
    print("DEMO – F4 en Q[x, y], orden grlex")
    print("  I = ⟨x² − y,  xy − 1⟩")
    print("=" * 60)
    R = Ring(['x', 'y'], order=grlex, char=0)
    f1 = R.poly({(2,0):1, (0,1):-1})
    f2 = R.poly({(1,1):1, (0,0):-1})
    G = f4_reduced([f1, f2], verbose=True)
    print(f"\nBase de Gröbner reducida (F4):")
    for i, g in enumerate(G):
        print(f"  g{i+1} = {g}")


def demo_comparacion():
    print("\n" + "=" * 60)
    print("DEMO – Comparación Buchberger vs F4")
    print("  Sistema en Q[x, y, z], orden grevlex")
    print("=" * 60)
    R = Ring(['x','y','z'], order=grevlex, char=0)
    f1 = R.poly({(2,0,0):1, (0,1,0):-1})           # x² − y
    f2 = R.poly({(1,1,0):1, (0,0,1):-1})           # xy − z
    f3 = R.poly({(0,2,0):1, (1,0,0):-1, (0,0,1):1}) # y² − x + z
    comparar_buchberger_f4([f1, f2, f3])


if __name__ == "__main__":
    demo_macaulay_matrix()
    demo_f4_sistema_cuadratico()
    demo_comparacion()
