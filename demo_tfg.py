"""
DEMOSTRACIÓN COMPLETA DEL TFG
==============================
TFG – Grado en Matemáticas Aplicadas – Universidad Nebrija
"Bases de Gröbner y sus Aplicaciones en Criptografía Multivariante"

Ejecuta todos los ejemplos del trabajo en secuencia, reproduciendo
los resultados de los capítulos 3, 4, 5 y 6.

Uso:
    python3 demo_tfg.py
    python3 demo_tfg.py --capitulo 3    (solo capítulo 3)
    python3 demo_tfg.py --capitulo 6    (solo aplicaciones)
"""

import sys
import time

# ─── Importar módulos del TFG ────────────────────────────────
from algoritmos_groebner import (
    Ring, Polynomial, lex, grlex, grevlex,
    reduced_groebner_basis, remainder,
    ideal_membership, elimination_ideal,
    demo_ordenes_monomiales, demo_division,
    demo_buchberger_Q, demo_buchberger_Fp, demo_eliminacion,
)
from f4_simplificado import (
    demo_macaulay_matrix, demo_f4_sistema_cuadratico,
    demo_comparacion,
)
from aplicaciones_criptografia import (
    UOV_Toy, hfe_toy, cstar_toy_attack,
    mq_attack_groebner, hybrid_attack,
    complexity_analysis, demo_mq, demo_uov,
)


SEPARADOR = "\n" + "█" * 60 + "\n"


# ══════════════════════════════════════════════════════════════
#  CAPÍTULO 3 – BASES DE GRÖBNER Y RESOLUCIÓN ALGORÍTMICA
# ══════════════════════════════════════════════════════════════

def demo_capitulo3():
    print(SEPARADOR)
    print("CAPÍTULO 3 – BASES DE GRÖBNER Y RESOLUCIÓN ALGORÍTMICA")
    print(SEPARADOR)

    # ── 3.1 Órdenes monomiales ────────────────────────────────
    demo_ordenes_monomiales()

    # ── 3.2 División multivariante ────────────────────────────
    demo_division()

    # ── 3.3 Bases de Gröbner: Buchberger en Q ────────────────
    demo_buchberger_Q()

    # ── 3.4 Buchberger sobre F_p ──────────────────────────────
    demo_buchberger_Fp()

    # ── 3.5 Teorema de eliminación ────────────────────────────
    demo_eliminacion()

    # ── 3.6 Ejemplo adicional: sistema de tres variables ──────
    print("\n" + "=" * 60)
    print("DEMO 6 – Buchberger en Q[x,y,z], orden lex")
    print("  I = ⟨xz − y²,  x³ − z²⟩  (curva algebraica)")
    print("=" * 60)
    R = Ring(['x', 'y', 'z'], order=lex, char=0)
    f1 = R.poly({(1,0,1): 1, (0,2,0): -1})    # xz − y²
    f2 = R.poly({(3,0,0): 1, (0,0,2): -1})    # x³ − z²
    G = reduced_groebner_basis([f1, f2], verbose=False)
    print(f"\n  Base de Gröbner reducida (lex):")
    for i, g in enumerate(G):
        print(f"  g{i+1} = {g}")
    # Ideal de eliminación I_1 (sin x)
    elim1 = [g for g in G if all(m.exp[0] == 0 for m in g.terms)]
    print(f"\n  Ideal de eliminación I_1 = I ∩ Q[y,z]: {elim1[0] if elim1 else '(vacío)'}")


# ══════════════════════════════════════════════════════════════
#  CAPÍTULO 4 – ALGORITMO DE BUCHBERGER DETALLADO
# ══════════════════════════════════════════════════════════════

def demo_capitulo4():
    print(SEPARADOR)
    print("CAPÍTULO 4 – ALGORITMO DE BUCHBERGER Y OPTIMIZACIONES")
    print(SEPARADOR)

    print("\n" + "=" * 60)
    print("DEMO – Ejecución de Buchberger con traza completa")
    print("  I = ⟨x² + y² − 1,  x² + y − 1⟩ en Q[x,y], lex")
    print("  (Intersección: parábola y = 1 − x², círculo x²+y²=1)")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f1 = R.poly({(2,0):1, (0,2):1, (0,0):-1})   # x² + y² − 1
    f2 = R.poly({(2,0):1, (0,1):1, (0,0):-1})   # x² + y − 1
    print(f"\n  f1 = {f1}")
    print(f"  f2 = {f2}")
    G = reduced_groebner_basis([f1, f2], verbose=True)
    print(f"\n  Base de Gröbner reducida:")
    for i, g in enumerate(G):
        print(f"    g{i+1} = {g}")
    # Leer soluciones del polinomio en y
    univar = [g for g in G if all(m.exp[0] == 0 for m in g.terms)]
    if univar:
        print(f"\n  Polinomio en y: {univar[0]}")
        print(f"  Soluciones:  y = 0 → x² = 1 → x = ±1")
        print(f"               y = 1 → x² = 0 → x =  0")
        print(f"  Puntos de intersección: (1,0), (−1,0), (0,1)")

    # Demostración del criterio del producto
    print("\n" + "=" * 60)
    print("DEMO – Criterio del producto de Buchberger")
    print("  f = x² + y  y  g = z³ − 1  (monomios líderes coprimos)")
    print("=" * 60)
    R2 = Ring(['x', 'y', 'z'], order=grlex, char=0)
    f = R2.poly({(2,0,0):1, (0,1,0):1})
    g = R2.poly({(0,0,3):1, (0,0,0):-1})
    from algoritmos_groebner import s_polynomial
    sp = s_polynomial(f, g)
    r = remainder(sp, [f, g])
    print(f"\n  f = {f},  LM(f) = x²")
    print(f"  g = {g},  LM(g) = z³")
    print(f"  gcd(x², z³) = 1 → criterio del producto aplicable")
    print(f"  S(f,g) = {sp}")
    print(f"  Resto de S(f,g) módulo {{f,g}} = {r}  (esperado: 0)")


# ══════════════════════════════════════════════════════════════
#  CAPÍTULO 5 – F4 Y F5
# ══════════════════════════════════════════════════════════════

def demo_capitulo5():
    print(SEPARADOR)
    print("CAPÍTULO 5 – ALGORITMOS F4 Y F5")
    print(SEPARADOR)

    # ── F4: matriz de Macaulay ─────────────────────────────────
    demo_macaulay_matrix()

    # ── F4 completo ────────────────────────────────────────────
    demo_f4_sistema_cuadratico()

    # ── Comparación F4 vs Buchberger ───────────────────────────
    demo_comparacion()

    # ── Demostración de grado de regularidad ──────────────────
    print("\n" + "=" * 60)
    print("DEMO – Impacto del grado de regularidad")
    print("  Sistema cuadrático sobre F_2: n ecuaciones, n variables")
    print("=" * 60)
    print("\n  n   d_reg   #monomios(n+d,d)   log10(C)")
    print("  " + "-"*45)
    from math import comb, log10
    for n in [4, 6, 8, 10]:
        d = n // 2 + 1
        binom = comb(n + d, d)
        c = binom ** 2.37
        print(f"  {n:>3}  {d:>5}   {binom:>16,}   {log10(c):>8.1f}")

    # ── F5: idea de firmas ─────────────────────────────────────
    print("\n" + "=" * 60)
    print("DEMO – Idea central de F5: criterio de sizygia")
    print("  I = ⟨f1, f2⟩ = ⟨x² − y, xy − 1⟩  en Q[x,y], lex")
    print("=" * 60)
    R = Ring(['x', 'y'], order=lex, char=0)
    f1 = R.poly({(2,0):1, (0,1):-1})
    f2 = R.poly({(1,1):1, (0,0):-1})
    from algoritmos_groebner import s_polynomial, buchberger
    G0 = buchberger([f1, f2], verbose=False)
    f3 = G0[2]   # x − y²
    print(f"\n  f1 = {f1},  sig = e1")
    print(f"  f2 = {f2},  sig = e2")
    print(f"  f3 = {f3},  sig = y·e1  (de S(f1,f2) = y·f1 − x·f2)")
    print(f"\n  Par (f1, f3):")
    print(f"  S(f1,f3) tiene firma x·sig(f3) = xy·e1")
    sp13 = s_polynomial(f1, f3)
    r13  = remainder(sp13, G0)
    print(f"  S(f1,f3) = {sp13}")
    print(f"  Resto = {r13}  {'← cubierto por sizygia de (f1,f2), F5 lo evita' if r13.is_zero() else ''}")
    print(f"\n  → F5 habría descartado este par sin calcularlo,")
    print(f"    ahorrando exactamente esta reducción.")


# ══════════════════════════════════════════════════════════════
#  CAPÍTULO 6 – APLICACIONES CRIPTOGRÁFICAS
# ══════════════════════════════════════════════════════════════

def demo_capitulo6():
    print(SEPARADOR)
    print("CAPÍTULO 6 – APLICACIONES EN CRIPTOGRAFÍA MULTIVARIANTE")
    print(SEPARADOR)

    # ── Problema MQ ────────────────────────────────────────────
    demo_mq()

    # ── C* toy ─────────────────────────────────────────────────
    cstar_toy_attack(n=3, p=2, theta=1)

    # ── HFE toy ────────────────────────────────────────────────
    hfe_toy(n=4, p=2, D=4, seed=7)

    # ── UOV ────────────────────────────────────────────────────
    demo_uov()

    # ── Verificación de la seguridad de UOV ───────────────────
    print("\n" + "=" * 60)
    print("DEMO – Ataque de Kipnis–Shamir a OV balanceado (v=o)")
    print("  Cuando v=o, el subespacio de aceite puede recuperarse")
    print("  con O(o) operaciones sobre las matrices públicas.")
    print("=" * 60)
    print("""
  Principio algebraico (Teorema 7.33, capítulo 6):
  
  Sea {P_k} el sistema público de un esquema OV con v = o.
  Para cualquier par de vectores de aceite o, o' ∈ Oil-space:
  
    ∑_k λ_k · F_k(o, o') = 0  para todo λ ∈ ker(M_{aceite})
  
  donde M_{aceite} es la matriz cuadrática evaluada en el
  subespacio de aceite.
  
  El subespacio de aceite es el núcleo de la combinación lineal
  Σ_k λ_k P_k, y puede encontrarse eficientemente por álgebra
  lineal (coste polinómico en n).
  
  Por ello, UOV requiere v > o (típicamente v ≥ 2o).
""")

    # ── Enfoque híbrido ────────────────────────────────────────
    print("=" * 60)
    print("DEMO – Análisis de complejidad y enfoque híbrido")
    print("=" * 60)
    complexity_analysis(n_values=[5, 10, 15, 20, 25, 30])


# ══════════════════════════════════════════════════════════════
#  EJECUCIÓN PRINCIPAL
# ══════════════════════════════════════════════════════════════

CAPITULOS = {
    3: ("Capítulo 3: Bases de Gröbner",       demo_capitulo3),
    4: ("Capítulo 4: Algoritmo de Buchberger", demo_capitulo4),
    5: ("Capítulo 5: F4 y F5",                demo_capitulo5),
    6: ("Capítulo 6: Aplicaciones cripto",    demo_capitulo6),
}

if __name__ == "__main__":
    # Parsear argumento --capitulo N (opcional)
    cap_sel = None
    if "--capitulo" in sys.argv:
        idx = sys.argv.index("--capitulo")
        if idx + 1 < len(sys.argv):
            cap_sel = int(sys.argv[idx + 1])

    t_inicio = time.perf_counter()

    if cap_sel is not None:
        if cap_sel not in CAPITULOS:
            print(f"Capítulo {cap_sel} no existe. Disponibles: {list(CAPITULOS.keys())}")
            sys.exit(1)
        titulo, fn = CAPITULOS[cap_sel]
        print(f"\n{'▓'*60}")
        print(f"  TFG – Demostración: {titulo}")
        print(f"{'▓'*60}")
        fn()
    else:
        print(f"\n{'▓'*60}")
        print("  TFG – DEMOSTRACIÓN COMPLETA")
        print("  Bases de Gröbner y Criptografía Multivariante")
        print(f"{'▓'*60}")
        for cap_num, (titulo, fn) in sorted(CAPITULOS.items()):
            t0 = time.perf_counter()
            fn()
            print(f"\n  [Capítulo {cap_num} completado en {(time.perf_counter()-t0)*1000:.0f} ms]")

    print(f"\n{'▓'*60}")
    print(f"  Demostración completada en {(time.perf_counter()-t_inicio)*1000:.0f} ms")
    print(f"{'▓'*60}\n")
