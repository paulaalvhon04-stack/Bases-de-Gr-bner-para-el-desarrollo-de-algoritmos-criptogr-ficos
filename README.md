# Bases de Gröbner y Criptografía Multivariante

**Trabajo de Fin de Grado – Grado en Matemáticas Aplicadas**  
Universidad Nebrija · Curso 2025–2026

> Implementación en Python de los algoritmos desarrollados en el TFG  
> *"Bases de Gröbner y sus Aplicaciones en Criptografía Multivariante"*

---

## Descripción

Este repositorio contiene la implementación **desde cero**, sin librerías  
de álgebra computacional, de los algoritmos estudiados en el trabajo:

| Archivo | Contenido |
|---|---|
| `algoritmos_groebner.py` | Polinomios, órdenes monomiales, división, S-polinomio, Buchberger, base reducida |
| `f4_simplificado.py` | Algoritmo F₄ con matrices de Macaulay y eliminación gaussiana |
| `aplicaciones_criptografia.py` | Problema MQ, C*, HFE, UOV, Rainbow, enfoque híbrido |
| `demo_tfg.py` | Demostración completa de todos los ejemplos del trabajo |

---

## Requisitos

```
Python >= 3.8
numpy
```

Instalar dependencias:

```bash
pip install numpy
```

---

## Uso

### Demostración completa
```bash
python3 demo_tfg.py
```

### Por capítulo
```bash
python3 demo_tfg.py --capitulo 3   # Bases de Gröbner
python3 demo_tfg.py --capitulo 4   # Algoritmo de Buchberger
python3 demo_tfg.py --capitulo 5   # Algoritmos F4 y F5
python3 demo_tfg.py --capitulo 6   # Aplicaciones criptográficas
```

### Módulos individuales
```bash
python3 algoritmos_groebner.py       # Buchberger y órdenes monomiales
python3 f4_simplificado.py           # F4 con matrices de Macaulay
python3 aplicaciones_criptografia.py # Criptosistemas multivariantes
```

---

## Ejemplos de salida

### Buchberger en Q[x,y], orden lex
```
I = ⟨x² − y,  xy − 1⟩
It. 1  par(0,1)  S-pol = x − y²  →  r = x − y²  *** nuevo generador
It. 2  par(0,2)  S-pol = xy² − y  →  r = 0
It. 3  par(1,2)  S-pol = y³ − 1  →  r = y³ − 1  *** nuevo generador
...
Base de Gröbner reducida:  g1 = x − y²,  g2 = y³ − 1
```

### UOV toy sobre F₇ (firma y verificación)
```
Vinagre: [4, 3]
Aceite:  [2, 2]
Verificación de la firma: VÁLIDA ✓
```

### Análisis de complejidad (ataque directo F4/F5)
```
 n  d_reg    C(n+d,d)   log₁₀(C)   factible
10      6       8,008        9.3         Sí
20     11  84,672,315       18.8     Límite
30     16  991,493...       28.4         No
```

---

## Estructura del código

### `algoritmos_groebner.py`
- **`Monomial`** — tupla de exponentes con multiplicación, división exacta, lcm y detección de coprimicidad
- **`Ring`** — contexto algebraico k[x₁,…,xₙ] con aritmética exacta (Fraction sobre ℚ, mod p sobre 𝔽ₚ)
- **`Polynomial`** — representación como dict {Monomial → coeficiente} con aritmética completa
- **`lex`, `grlex`, `grevlex`** — tres órdenes monomiales según las definiciones del capítulo 3
- **`division(f, [f₁,…,fₛ])`** — algoritmo de división multivariante con cocientes y resto
- **`s_polynomial(f, g)`** — cancelación del término líder mediante el mcm
- **`buchberger(G)`** — con criterio del producto y criterio de la cadena
- **`reduced_groebner_basis(G)`** — base mínima, mónicos, reducción cruzada

### `f4_simplificado.py`
- **`build_macaulay_matrix`** — construye la matriz de Macaulay con preprocesado simbólico
- **`gaussian_elimination`** — sobre ℚ (punto flotante) y 𝔽ₚ (aritmética modular exacta)
- **`f4`** — selección por grado mínimo, reducción matricial por lotes, actualización de la base

### `aplicaciones_criptografia.py`
- **`mq_attack_groebner`** — ataque directo al problema MQ con ecuaciones de campo xᵢᵖ − xᵢ
- **`UOV_Toy`** — clave privada, clave pública, firma (resolución de sistema lineal) y verificación
- **`hfe_toy`** — sistema público HFE con parámetro D y ataque algebraico directo
- **`hybrid_attack`** — búsqueda exhaustiva en k variables + Gröbner en las n−k restantes
- **`complexity_analysis`** — tabla dᵣₑg, complejidad y factibilidad para n = 5…30

---

## Correspondencia con el TFG

| Módulo | Capítulo del TFG |
|---|---|
| `algoritmos_groebner.py` | Cap. 3 – Bases de Gröbner y Resolución Algorítmica |
| `algoritmos_groebner.py` | Cap. 4 – El Algoritmo de Buchberger |
| `f4_simplificado.py` | Cap. 5 – Algoritmos F₄ y F₅ |
| `aplicaciones_criptografia.py` | Cap. 6 – Aplicaciones en Criptografía Multivariante |

---

## Referencias

- D. Cox, J. Little, D. O'Shea – *Ideals, Varieties, and Algorithms*, Springer, 2005
- J.-C. Faugère – *A new efficient algorithm for computing Gröbner bases (F4)*, 1999
- J. Patarin – *Hidden Fields Equations (HFE)*, EUROCRYPT 1996
- W. Beullens – *Breaking Rainbow takes a weekend on a laptop*, CRYPTO 2022
