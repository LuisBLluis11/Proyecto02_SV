(** Semántica y verificación 22-1
  
  Árboles de Braun
  
  Los árboles de Braun sirven como una estructura de datos 
  donde las consultas, eliminaciones y extensiones pueden ser
  bastante rápidas. Los árboles de Braun son árboles
  binarios balanceados. 
  En este script con se plantea la definición de un árbol de Braun
  y algunas de sus propiedades básicas. Dado que se requiere
  que los árboles sean balanceados, requerimos plantear propiedades
  respecto a tamaños de árboles. Requerimos que el tamaño 
  de todo subárbol hermano difiera en a lo más una unidad. Esto impone 
  descripciones de los tamaños referirá mucho dividir un natural en dos. 
  La descripción usual mediante sucesores es incómoda para constantes
  divisiones entre dos, por lo que se usa su representación binaria
  al esta ser mucho más amena a lo requerido. 


  Este script fue basado de los cursos de Favio Ezquiel
  Miranda Perea y modificado en ciertos aspectos.
  
  Edición por Luis Felipe Benítez Lluis

  Contenido:
    1 Definición de función de tamaño
    2 Propiedad de balance de árboles de Braun
    3 Propiedades de tamaño
        
        
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. *)
From Proyecto02Base Require Import binnat.
From Proyecto02Base Require Import order_binnat.
From Proyecto02Base Require Import bintree.
Require Import Coq.Arith.PeanoNat.


(** >1 Definición de función de tamaño*)

(* Función de tamaño de un árbol como número binario*)
Fixpoint bsize (t:BTree): BN :=
 match t with
  E => Z
 |N x s t =>  sucBN ((bsize s) +_(bsize t))
 end.

Check bsize.

(** >E Rellenar este problema. Dificultad 2*)
Lemma bsize_Z: forall (t:BTree), bsize t = Z -> t = E.
Proof.
Admitted.

Lemma bsize_nonZ: forall (t:BTree), t <> E <-> bsize t <> Z.
Proof.
intros.
split.
intro.
contradict H.
apply bsize_Z.
trivial.
intro.
intro.
contradict H.
rewrite H0.
simpl.
reflexivity.
Qed.


Lemma btNonE: forall (t:BTree) (b:BN), t <> E -> 
                       exists (b:BN), bsize t = U b \/ bsize t = D b.
Proof.
intros.
apply bsize_nonZ in H.
apply (bnNonZ (bsize t)) in H.
trivial.
Qed.




(** >2 Propiedad de balance de árboles de Braun*)
(* Prop para decir que una árbol está balanceado *)
Inductive bbal : BTree -> Prop:= 
 |bbalE : bbal E (*El árbol vacio está balanceado*)
 |bbalN : forall (a: A) (s t: BTree), (* tomamos s t los hijos y a:A*)
          bbal s -> bbal t -> (* si los árboles hijos están balanceados*)
            (bsize t) <=BN (bsize s) ->  (*El tamaño t supera a s*) 
            (bsize s) <=BN (sucBN (bsize t)) -> (* Pero lo supera en a lo mas uno*)
                                      bbal (N a s t).
(*Con estas reglas la diferencia entre tamaños de los hijos es a lo más
1*)

Check bbal_ind.

(*Como todas las propiedades en adelante se harán sobre árboles que cumplan
ser de Braun, se asumirá que son balanceados, y por tanto añadimos
tal afirmación global*)
Parameter (allBal: forall (t:BTree), bbal t).





(** >3 Propiedades de tamaño*)

Lemma prop_0_U : 
  forall (a:A) (s t:BTree) (b:BN), 
         bbal (N a s t) -> 
         bsize(N a s t) = U b -> 
                  bsize s = b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_U in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0.
apply plus_a_a in H0.
rewrite <- H8.
intuition.
rewrite H8 in H0b.
rewrite plus_D in H0b.
inversion H0b.
Qed.


Lemma prop_0_D : 
  forall (a:A) (s t:BTree) (b:BN), 
    bbal (N a s t) -> 
    bsize(N a s t) = D b -> 
        bsize s = sucBN b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_D in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0b.
rewrite plus_U in H0b.
inversion H0b.
rewrite H8 in H0.
apply plus_SucBNa_a in H0.
rewrite <- H0.
intuition.
Qed.

Corollary size_caseU: 
  forall (a:A) (l r:BTree) (b:BN), 
    bsize (N a l r) = U b -> 
        bsize l = bsize r.
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_U a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary size_caseD: 
    forall (a:A) (l r:BTree) (b:BN), 
        bsize (N a l r) = D b -> 
            bsize l = sucBN (bsize r).
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_D a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary bbal_size_r: 
    forall (a:A) (l r:BTree), 
        bsize (N a l r) = U (bsize r) \/ 
                 bsize (N a l r) = D (bsize r).
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
simpl.
assert (Z <> sucBN (bsize l +_bsize r)).
apply ZnotSucBN.
intuition.
destruct H.
apply prop_0_U in H.
simpl.
destruct H.
rewrite H.
rewrite H0.
rewrite plus_U.
intuition.
trivial.
apply prop_0_D in H.
destruct H.
simpl.
rewrite H.
rewrite H0.
rewrite plus_D.
intuition.
trivial.
Qed.

Theorem bbal_size_r2: 
  forall (a:A) (l r:BTree), 
      (bsize (N a l r)) <=BN (D (bsize r)). 
Proof.
intros a l r.
destruct (bbal_size_r a l r).
constructor.
rewrite H.
constructor.
rewrite H.
constructor.
Qed.

Theorem bbal_size_l: 
  forall (a:A) (l r:BTree), 
      (bsize (N a l r)) <=BN (U (bsize l)). 
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
- simpl.
  assert (Z <> sucBN (bsize l +_bsize r)).
  apply ZnotSucBN.
  intuition.
- destruct H.
  + apply prop_0_U in H.
    * simpl.
      destruct H.
      subst.
      rewrite H0. 
      rewrite plus_U.
      constructor.
    * assumption.
  +  apply prop_0_D in H.
    * simpl.
      destruct H.
rewrite H.
rewrite H0.
rewrite plus_D.
constructor.
constructor.
apply lts.
* trivial.
Qed.


          

Lemma lt_U_bsize: forall (b:BN) (a:A) (t1 t2:BTree), 
    (U b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t1).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) <=BN (U (bsize t1))).
apply bbal_size_l.
assert ((U b) <BN (U (bsize t1))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Theorem rightE: forall (a:A) (t1 t2:BTree), 
    bbal(N a t1 t2) -> t2 = E -> 
        (t1 = E \/ exists (aa:A), t1 = (N aa E E)).
Proof.
intros.
inversion H.
destruct (bbalCond_eqs (bsize t1) (bsize t2)).
trivial.
trivial.
rewrite H0 in H8.
simpl in H8.
apply bsize_Z in H8.
intuition.
rewrite H0 in H8.
right.
destruct t1.
simpl in H8.
inversion H8.
simpl in H8.
replace (U Z) with (sucBN Z) in H8.
apply SucBNinj in H8.
apply plusBN_Z_Z in H8.
destruct H8.
apply bsize_Z in H8.
apply bsize_Z in H9.
exists a1.
rewrite H8.
rewrite H9.
trivial.
intuition.
Qed.


Lemma lt_D_bsize: forall (b:BN) (a:A) (t1 t2:BTree), 
      (D b) <BN (bsize (N a t1 t2)) -> 
          b <BN (bsize t2).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) <=BN (D (bsize t2))).
apply bbal_size_r2.
assert ((D b) <BN (D (bsize t2))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.


(** >E Rellenar este problema. Dificultad 1*)
Lemma bbal_leaf: forall (a:A), bbal (N a E E).
Proof.
Admitted.



Theorem leftE_leaf: forall (t1 t2:BTree) (a:A), 
    bbal (N a t1 t2) -> 
    t1 = E -> 
        t2 = E.
Proof.
intros t1 t2 c HBal H.
inversion HBal.
rewrite H in H5.
simpl in H5.
inversion H5.
apply bsize_Z in H9.
trivial.
inversion H7.
Qed.


(** >E ¿Te atreves a resolver este? Dificultad ?? 
      (no obligatorio)*)
Lemma bbal_inv: 
    forall (t:BTree), t <> E ->  
        (exists (z:A), t = N z E E)  \/ 
            exists (z:A) (r1 r2:BTree), 
                  bbal r1 /\ bbal r2 /\ r1 <> E /\ t = N z r1 r2.
Proof.
Admitted.
