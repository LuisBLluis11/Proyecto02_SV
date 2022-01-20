# Proyecto 02 Semántica y Verificación 2022-1
Manuel Soto Romero

Luis Felipe Benítez Lluis

Fecha Límite de entrega: 23:59hrs domingo 30/enero/2022

Fecha de Exposición: Martes 1/febrero/2022 

Estos scripts son versiones modificadas de scripts diseñados por Favio Ezequiel Miranda Perea.

---
## Arreglos Flexibles
Este repositorio contiene la implementación de arreglos flexibles mediante árboles de Braun en coq. Para desarrollar esta estructura de datos se requiere de una versión de números binarios junto ocn sus propiedades. 

### Contenido
El siguiente repositorio se divide en los siguientes scripts. El orden de complilación es el provtisto por esta lísta


1. [binnat.v](binnat.v) En este script se definen los números binarios
	 y se desarrollan las propiedades básicas de éstos.
2. [order_binnat.v](order_binnat.v) En este script se define el orden para los números binarios así como teoremas y propiedades de éstos. 
3. [bintree.v](bintree.v) En este script se definen los árboles binarios.
4. [braunT.v](braunT.v) En este script se definen los árboles de Braun basándose de la definición de árbol binario. Se muestras muchas de las propiedades básicas de esta estructura.
5. [lookup_BT.v](lookup_BT.v) En este script se definen las funciones de consulta `lookup` y `update` y se muestran unas pocas propiedades.
6. [Ext_Rem_BT.v](Ext_Rem_BT.v) En este script se definen las funciones `le`,`lr`,`he`,`hr` y se muestrans propiedades de seguridad respecto a estas funciones. 

Se deberá completar las pruebas de los siguientes ejercicios. 


*   [binnat.v](binnat.v) `SucBNinj`, `plusComm`, `inverse_op_1`.
*   [order_binnat.v](order_binnat.v) `lt_asuc_iff_UD`, `ltBN_suc_mono_r`,`lt_trichotomy`.
*   [braunT.v](braunT.v) `bbal_leaf`, `bsize_Z`; opcional `bbal_inv`
* [Ext_Rem_BT.v](Ext_Rem_BT.v) `bal_le`, `bsize_he`, `bal_he`, así como la definición de `he`.
* Se deberrá entregar una solución a mano de alguno de los ejercicios de
[Ext_Rem_BT.v](Ext_Rem_BT.v) de los ejercicios `lr_le_inv`,`he_last`,`bsize_lr_pred_bsize`,`he_hasroot`.

Los ejercicios tienen un grado de dificultad en un rango 1-5, donde 1 es muy sencillo y 5 muy complicado. El juicio de complicado refiere mayoritariamente a la longitud de la prueba que se tiene, pero es posible que haya pruebas más cortas y por tanto el ejercicio sea
mas sencillo. En algunos ejercicios se ofrece una parte parcial de la prueba, y en otros se da alguna sugerencia.

---
## Información del Alumno

* Nombre: 
* Problema elegido para solución a mano:

### Observaciones sobre sus soluciones.
