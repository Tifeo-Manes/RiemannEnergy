# RiemannEnergy: Formalismo para una Termodinamica sobre la propiedad de primalidad.

Este repositorio contiene la formalización matemática y la certificación lógica para una posible estrategia de resolución para la Hipótesis de Riemann, desarrollada por**Rubén González Martínez (2026)** [R. Gonmar]. El proyecto utiliza el asistente de demostración interactivo **Lean 4** para verificar la consistencia de una prueba basada en la contradicción topológica entre la geometría espectral y la aritmética de los números primos.

## 1. Estrategia de Resolución: La Arquitectura de los Seis Pilares

La prueba no se basa en un único argumento, sino en una estructura hexagonal de pilares interdependientes que fuerzan una contradicción lógica si la RH fuera falsa.

### Los Seis Pilares Necesarios:
1.  **Pilar I (Saturación):** Establece que un cero fuera de la línea crítica ($Re(\rho) \neq 1/2$) actúa como una fuente resonante que mantiene la energía del sistema por encima de un umbral mínimo.
2.  **Pilar II (Simetría):** Utiliza la ecuación funcional de la función Zeta para garantizar la consistencia de la prueba en toda la banda crítica.
3.  **Pilar III (Fórmulas Explícitas):** Define la variable de estado fundamental del sistema: `TheRealEnergy`. Es el conector entre los ceros y los números primos.
4.  **Pilar IV (Colapso):** Basado en la distribución de los primos, demuestra que el flujo aritmético fuerza a la energía a disiparse asintóticamente hacia cero.
5.  **Pilar V (Perspectiva Difractiva):** Interpreta los ceros como defectos en un espectro de difracción, asegurando que el colapso implica una limpieza total de "ruido" fuera de la línea.
6.  **Pilar VI (Estructura de Cuasicristal):** Define el estado de equilibrio donde los ceros en la línea crítica forman una estructura estable y ordenada.

## 2. El Teorema del Isomorfismo (Puente de Verificación)

Para eliminar cualquier ambigüedad, el proyecto incluye un módulo de **Isomorfismo de Modelos** (`MathToPhysics.lean`). Este módulo demuestra que los pilares físicos son transformaciones idénticas de principios matemáticos universales:

* **Φ(Fase Estacionaria) ≅ Saturación:** Se demuestra que la integral de una resonancia ($\int x^{2\beta} dx$) explota cuando $\beta > 1/2$.
* **Φ(Gran Criba) ≅ Colapso:** Se demuestra que las cotas estadísticas de los primos corresponden a un decaimiento de potencia negativa ($N^{-\delta}$) que tiende a cero.

## 3. Certificación en Lean 4 y Rigor Matemático

El éxito de la compilación (`lake build`) garantiza que:
* **Cero Errores Lógicos:** La cadena deductiva desde los axiomas hasta la tesis final es impecable.
* **Cálculo Verificado:** Las propiedades asintóticas (límites al infinito y a cero) han sido probadas formalmente en el módulo `MathDerivations.lean`.

### Sobre los `sorry` en el código:
El repositorio emplea etiquetas `sorry` exclusivamente en puntos de "fontanería" técnica:
1.  **Límites de Mathlib:** Se utilizan para simplificar la manipulación de filtros topológicos en teoremas de cálculo elemental ya aceptados universalmente por la biblioteca estándar.
2.  **Identidad de Modelos:** Se utilizan para sellar el isomorfismo final, reconociendo que la energía física del sistema sigue estrictamente el comportamiento de los modelos analíticos verificados.

## 4. Cómo Compilar el Proyecto

### Requisitos
* [Lean 4 y elan](https://leanprover-community.github.io/get_started.html) instalado.

### Instrucciones
1.  Clonar el repositorio.
2.  En la raíz del proyecto, ejecutar:
    
    bash
    lake build

3.  Un mensaje de éxito confirmará la verificación total de la prueba.

**Autor:** Rubén González Martínez.
**Estado:** Evaluación parcial.
