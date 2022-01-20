(** Semántica y verificación 22-1
  
  Orden para binarios

  Script con las definiciones y las propiedades de 
  orden en naturales binarios.  
  Este árbol binarios será sobre el cual se definan los árboles de braun.
  Este script fue basado de los cursos de Favio Ezquiel
  Miranda Perea y modificado en ciertos aspectos.
  
  Edición por Luis Felipe Benítez Lluis

  Contenido:
    1 Definiciones de orden en binnat 
    2 Propiedades de <BN en operadores U y D
    3 Axiomas de COPO estricto para <BN
    4 Propiedades de <BN con cero
    5 Propiedades de suc sin dependencias
    6 Propiedades trasformación de representaciones
    7 Mas propiedades de <BN con sucesor
    8 Propiedades de <=BN
    9 Propiedadese que combinan <BN y <=BN
    10 Axiomas de COPO para <BN
    11 Propiedades de orden <BN respecto a pred 
        
        
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. *)


Require Import Coq.Arith.PeanoNat.
From Proyecto02Base Require Import binnat.
From Coq Require Import Lia.



(** >1 Definiciones de orden en binnat *)
Inductive ltBN : BN -> BN -> Prop :=
 | ltBNZU : forall (a:BN), ltBN Z (U a)
 | ltBNZD : forall (a:BN), ltBN Z (D a)
 | ltBNUU : forall (a b:BN), ltBN a b -> ltBN (U a) (U b)
 | ltBNUDeq : forall (a :BN), ltBN (U a) (D a) 
 | ltBNUD : forall (a b:BN), ltBN a b -> ltBN (U a) (D b) 
 | ltBNDU : forall (a b:BN), ltBN a b -> ltBN (D a) (U b)
 | ltBNDD : forall (a b:BN), ltBN a b -> ltBN (D a) (D b).


Inductive lteqBN: BN -> BN -> Prop :=
 | lteqBNref: forall (a:BN), lteqBN a a
 | lteqBNl: forall (a b: BN), ltBN a b -> lteqBN a b.


Notation "a <BN b" := (ltBN a b) (at level 70).
Notation "a <BN b <BN c" := (ltBN a b /\ ltBN b c) (at level 70, b at next level).

Notation "a <=BN b" := (lteqBN a b) (at level 70).




(** >2 Propiedades de <BN en operadores U y D*)  
Lemma lt_Ua_and_Da: forall a:BN, a<BN U a/\ a <BN D a.
Proof.
induction a.
- split; constructor.
- destruct IHa as [HU HD]. split; constructor; assumption.
- destruct IHa as [HU HD]. split; constructor; assumption.
Qed.
Lemma lt_Ua: forall a:BN , a<BN U a.
Proof.
intros.
pose proof lt_Ua_and_Da a.
destruct H.
assumption.
Qed.

Lemma lt_Da: forall a:BN , a<BN D a.
Proof.
intros.
pose proof lt_Ua_and_Da a.
destruct H.
assumption.
Qed.
Lemma lt_UaDa: forall a:BN, U a <BN D a.
Proof.
apply ltBNUDeq.
Qed.

Lemma lt_U: forall (a b:BN), a <BN b <-> (U a) <BN U b.
Proof.
intros.
split.
+ intro. 
  apply ltBNUU. 
  assumption.
+ intro.
  inversion H.
  assumption.
Qed.


Lemma lt_D: forall (a b:BN), a <BN b <-> (D a) <BN D b.
Proof.
intros. split.
+ intros. apply ltBNDD.
  assumption.
+ intros.
  inversion H.
  assumption.
Qed.




(** >3 Axiomas de COPO estricto para <BN*)
Lemma ltBN_arefl: forall (a:BN), ~ a <BN a.
Proof.
intros.
induction a.
unfold not.
intros.
inversion H.
contradict IHa.
inversion IHa.
trivial.
contradict IHa.
inversion IHa.
trivial.
Qed.

Create HintDb PNatDb.

Hint Resolve ltBN_arefl: PNatDb.

Lemma ltBN_asym: forall (a b:BN), a <BN b -> ~ b <BN a.
Proof.
intros.
induction H.
unfold not;intros.
inversion H.
unfold not;intros.
inversion H.
contradict IHltBN.
inversion IHltBN.
trivial.
unfold not;intros.
inversion H.
apply (ltBN_arefl a).
trivial.
(*exact (ltBN_arefl a H2).*)
unfold not;intros.
inversion H0.
intuition.
contradict IHltBN.
inversion IHltBN.
rewrite H2 in H.
trivial.
trivial.
contradict IHltBN.
inversion IHltBN.
trivial.
Qed.

Hint Resolve ltBN_asym: PNatDb.

Lemma ltBN_tr: forall (b c:BN), b <BN c -> forall (x:BN), x <BN b -> x <BN c.
Proof.
intro.
intro.
intro.
induction H.
- intros. inversion H.
- intros. inversion H.
- intros. destruct x.
  --  constructor.
  -- apply ltBNUU.
     apply IHltBN.
     inversion H0;subst;assumption.
  -- apply ltBNDU.
     apply IHltBN.
     inversion H0;subst;assumption.
     
  - intros. destruct x.
  --  constructor.
  -- apply ltBNUD.
     inversion H;subst;assumption.
  -- apply ltBNDD.
     inversion H;subst;assumption.

- intros. destruct x.
  --  constructor.
  -- apply ltBNUD.
     apply IHltBN.
     inversion H0;subst;assumption.
  -- apply ltBNDD.
     apply IHltBN.
     inversion H0;subst;assumption.
     
  - intros. destruct x.
  --  constructor.
  -- apply ltBNUU.
     inversion H0.
     assumption.
     apply IHltBN.
     assumption.
  -- apply ltBNDU.
     apply IHltBN.
     inversion H0;subst;assumption.
     
     
  - intros. destruct x.
  --  constructor.
  -- apply ltBNUD.
     inversion H0.
     assumption.
     apply IHltBN.
     assumption.
  -- apply ltBNDD.
     apply IHltBN.
     inversion H0;subst;assumption.
Qed.


Hint Resolve ltBN_tr: PNatDb.


Lemma ltBN_trans: forall (a b c:BN), a <BN b -> b <BN c -> a <BN c.
Proof.
intros.
eapply ltBN_tr.
eexact H0.
trivial.
Qed.




(** >4 Propiedades de <BN con cero*)
Lemma ltBN_ZUa: forall a:BN, Z <BN U a.
Proof.
induction a;try(constructor).
Qed.

Lemma ltBN_ZDa: forall a:BN, Z <BN D a.
Proof.
induction a;try(constructor).
Qed.

Lemma ltBN_UZDa: forall a:BN, U Z <BN D a.
Proof.
induction a;try(do 2 constructor).
Qed.
Lemma ltBN_Zsuca: forall a:BN,  Z <BN sucBN a.
Proof.
induction a;try(do 2 constructor).
Qed.

Lemma ltBN_aUZ: forall (a:BN), a <BN U Z -> a =Z.
Proof.
intros.
induction a.
reflexivity.
inversion H.
inversion H2.
inversion H.
inversion H2.
Qed.

Lemma ltBN_UaDZ: forall (a:BN),U a <BN D Z -> a =Z.
Proof.
induction a.
- reflexivity.
- intros. inversion H. subst. inversion H2.
- intros. inversion H. subst. inversion H2.
Qed.

Lemma ltBN_aDZ: forall (a:BN), a <BN D Z -> (a =Z \/ a= U Z).
Proof.
intros.
induction a.
- left. reflexivity.
- assert (a<BN D Z). 
  -- eapply ltBN_trans. 2:{ apply H. } apply lt_Ua.
  -- destruct IHa.
  --- assumption.
  --- right. subst. reflexivity.
  --- apply ltBN_UaDZ in H. subst. discriminate H1.
-  assert (a<BN D Z). 
  -- eapply ltBN_trans. 2:{ apply H. } apply lt_Da.
  -- destruct IHa.
  --- assumption.
  --- subst. contradict H. apply ltBN_arefl.
  --- inversion H. inversion H4.
Qed.

Lemma ltBM_UZDa: forall (a:BN), U Z <BN D a.
Proof.
induction a.
- constructor.
- do 2 constructor.
-  do 2 constructor.
Qed.





(** >5 Propiedades de suc sin dependencias*)
Lemma lts: forall (a:BN), a <BN (sucBN a).
Proof.
intros.
induction a.
constructor.
simpl.
constructor.
simpl.
constructor.
trivial.
Qed.

Lemma ltDUs: forall (a:BN), (D a) <BN (U (sucBN a)).
Proof.
intros.
induction a.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
trivial.
Qed.

Lemma lt_suc: forall a:BN, a <BN sucBN a.
Proof. 
induction a.
simpl. apply ltBN_ZUa.
simpl. apply ltBNUDeq.
simpl. apply ltDUs.
Qed.





(** >6 Propiedades trasformación de representaciones*)

Lemma le_ToN_order: forall (a b:BN),
  a <BN b -> toN a < toN b.
Proof.
intro.
induction a;intros.
-  inversion H. simpl.
    rewrite Nat.add_1_r. apply Nat.lt_0_succ.
   simpl. rewrite Nat.add_succ_r. apply Nat.lt_0_succ.
- simpl.
  inversion H.
  -- subst. simpl.
      apply IHa in H1.
      lia.
  -- subst. simpl.
      lia.
  -- subst. simpl.
     apply IHa in H1.
     lia. 
- simpl. inversion H. subst.
  -- simpl. apply IHa in H1.
     lia.
  -- subst. simpl.
    apply IHa in H1.
     lia.
Qed.  
 
Lemma le_ToBN_order: forall (b a: nat),
  a < b -> toBN a <BN toBN b.
Proof.
intro.
induction b;intros.
- simpl. inversion H.
- simpl.
  inversion H.
  --  apply lt_suc.
  -- simpl. inversion H1.
  --- subst. specialize (IHb a).
      pose proof Nat.lt_succ_diag_r a.
      apply IHb in H0.
      eapply ltBN_trans. 
      + apply H0.
      + apply lt_suc.
  --- subst.
      assert (a < S m0). 
      { eapply Nat.lt_le_trans.
        apply Nat.lt_succ_diag_r.
        assumption.
      }
      apply IHb in H0.
      eapply ltBN_trans.
      apply H0. 
      apply lt_suc.
Qed.

Lemma le_ToN_order_equiv: forall (a b:BN),
  a <BN b <-> toN a < toN b.
Proof.
split.
apply le_ToN_order.
remember (toN a) as aa.
remember (toN b) as bb.
intros.
assert (toBN aa = a).
  { subst. apply inverse_op_2.  }
assert (toBN bb = b).
  { subst. apply inverse_op_2. }
rewrite <- H0.
rewrite <- H1.
apply le_ToBN_order.
assumption.
Qed.

Lemma le_ToBN_order_equiv: forall (b a: nat),
  a < b <-> toBN a <BN toBN b.
Proof.
split.
apply le_ToBN_order.
remember (toBN a) as aa.
remember (toBN b) as bb.
intros.
assert (toN aa = a).
  { subst. apply inverse_op_1.  }
assert (toN bb = b).
  { subst. apply inverse_op_1. }
rewrite <- H0.
rewrite <- H1.
apply le_ToN_order.
assumption.
Qed.




(** >7 Mas propiedades de <BN con sucesor*)

Lemma lt_UsaDb:forall (b a:BN), a<BN b -> U (sucBN a) <BN D b.
Proof.
intros.
apply <-le_ToN_order_equiv.
simpl.
apply le_ToN_order_equiv in H.
rewrite toN_sucBN.
lia.
Qed.
  
(** >E Rellenar este problema. Dificultad 3. Lia es una táctica para resolver 
 problemas aritméticos simples.*)
Lemma lt_asuc_iff_UD: forall (a b:BN), a <BN  sucBN b <-> (U a) <BN D b.
Proof.

intros. split.
-
intros.
apply <-le_ToN_order_equiv.
simpl. apply le_ToN_order_equiv in H.
rewrite toN_sucBN in H.
lia.
- (*Concretar este caso*)
Admitted.

(** >E Rellenar este problema. Dificultad 3. Usar inducción sobre <BN y varias propiedades
        Dificultad 3*)
Lemma ltBN_suc_mono_r: forall (a b :BN), a<BN b -> sucBN a <BN sucBN b.
Proof.
Admitted.





(** >8 Propiedades de <=BN*)

Lemma lteqBN_Za: forall (a:BN), Z <=BN a.
Proof.
intros.
destruct a.
- constructor.
- constructor.
  apply ltBNZU.
- constructor.
  apply ltBNZD.
Qed.

Hint Resolve lts: PNatDb.

Lemma lteqs: forall (a:BN), a <=BN (sucBN a).
Proof.
intros.
induction a.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
inversion IHa.
contradict H0.
apply notSucBN.
trivial.
Qed.

Hint Resolve lteqs: PNatDb.

Lemma ltaux1: forall (j:BN), Z <=BN (D j) -> Z <=BN j.
Proof.
intros.
apply lteqBN_Za.
Qed.


Lemma lteqBN_refl : forall (b:BN), b <=BN b.
Proof.
intros.
constructor.
Qed.

Lemma lteqBN_Z : forall (b:BN), Z <=BN b.
Proof.
intros.
destruct b.
constructor.
constructor;constructor.
constructor;constructor.
Qed.

Lemma lteqBN_U_U:forall (a b:BN), (U a) <=BN (U b) <-> a <=BN b.
Proof.
intros.
split.
{
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
}
intros.
inversion H.
- subst.
constructor.
- subst. do 2 constructor. assumption.
Qed.

Lemma lteqBN_D_D : forall (a b : BN), (D a) <=BN (D b)<-> a <=BN b.
Proof.
intros.
split.
{
intro.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
}
intros.
inversion H.
-
subst.
constructor.
- subst. do 2 constructor.
assumption.
Qed.

Lemma lteqBN_U_D:forall (a b:BN), (U a) <=BN (D b) <-> a <=BN b.
Proof.
split.
{
intros.
inversion H.
inversion H0.
constructor.
constructor.
trivial.
}
intros.
inversion H.
- subst.  constructor.  constructor.
- subst. do 2 constructor. assumption.
Qed.

Lemma lteqBN_D_U:forall (a b:BN), (D a) <=BN (U b) -> a <=BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
trivial.
Qed.





(** >9 Propiedadese que combinan <BN y <=BN*)
Hint Resolve ltBN_trans: PNatDb.
Lemma le_noteq_lt: forall (a b :BN), a <> b -> a <=BN b -> a <BN b.
Proof.
 intros.
 inversion H0.
 - subst. contradict H. reflexivity.
 - assumption.
Qed.

Lemma lt_lteqBN_trans: forall (a b c:BN), a <BN b -> b <=BN c -> a <BN c.
Proof.
intros.
inversion H0.
rewrite H2 in H.
trivial.
eapply ltBN_trans.
eexact H.
trivial.
Qed.

Hint Resolve lt_lteqBN_trans: PNatDb.

Lemma lteqBN_trans: forall (a b c:BN), a <=BN b -> b <=BN c -> a <=BN c.
Proof.
intros.
inversion H.
trivial.
inversion H0.
rewrite H5 in H.
trivial.
constructor.
eapply ltBN_trans.
eexact H1.
trivial.
Qed.
Hint Resolve ltDUs: PNatDb.
Hint Resolve lteqBN_trans: PNatDb.

Lemma not_lt: forall (a b:BN), b <=BN a -> ~ a <BN b.
Proof.
intros.
destruct H.
-  apply ltBN_arefl.
- apply ltBN_asym. assumption.
Qed.

Lemma lt1: forall (b a:BN), a <BN (sucBN b) -> a <=BN b.
Proof.
intro.
induction b.
- intros.
  simpl.
  inversion H.
  constructor.
  inversion H2.
  inversion H2.
- intros. 
  inversion H.
  * apply lteqBN_Za.
  * constructor.
  * constructor.
    constructor.
    assumption.
  * constructor.
    constructor.
    assumption.
- intros.
  inversion H.
  * apply lteqBN_Za. 
  * subst.
    apply IHb in H2.
    inversion H2.
    -- subst. constructor.
      inversion H2;apply ltBNUDeq.
    -- subst. constructor.
     constructor. assumption.
 * subst. apply IHb in H2.
    inversion H2.
    -- subst. constructor.
    -- subst. constructor.
     constructor. assumption.
Qed.
     

Hint Resolve lt1: PNatDb.

Lemma lt2: forall (b a:BN), a <=BN b -> a <BN (sucBN b).
Proof.
intro.
induction b.
- intros.
  inversion H.
  subst.
  constructor.
  subst.
  inversion H0.
- intros.
  inversion H.
  subst.
  constructor.
  subst.
  induction a.
  constructor.
  inversion H0.
  subst.
  simpl.
  constructor.
  assumption.
  simpl.
  constructor.
  inversion H0.
  assumption.
- intros.
  inversion H.
  apply lts.
  subst.
  inversion H0.
  constructor.
  simpl.
  constructor.
  apply lts.
  simpl.
  subst.
  constructor.
  apply IHb.
  constructor.
  assumption.
  simpl.
  constructor.
  apply IHb.
  constructor.
  assumption.
Qed.
Lemma le_ab_lt_asucb: forall (b a:BN), a <=BN b <-> a <BN (sucBN b).
Proof.
intros.
split.
apply lt2.
apply lt1.
Qed.

Hint Resolve lt2: PNatDb.

Lemma lt_suc_lteq: forall (a b:BN), a <BN b <-> (sucBN a) <=BN b.
Proof.
intros.
split. 
+ intro. induction H.
- simpl. destruct a.
  -- constructor.
  -- simpl. constructor. 
     apply ltBNUU.
     constructor.
  -- constructor.
     apply ltBNUU.
     constructor. 
- destruct a;do 3 constructor.
  
- simpl.
  constructor.
  constructor.
  assumption.
- constructor.
- simpl.
  constructor.
  constructor.
  assumption.
- simpl.
  apply <-lteqBN_U_U.
  assumption.
- simpl. 
  apply <-lteqBN_U_D.
  assumption.
+ intro.
pose proof (lts a).
eapply lt_lteqBN_trans.
apply H0.
assumption.
Qed.
Lemma sucBN_lt: forall (a b:BN), sucBN a <> b -> a <BN b -> (sucBN a) <BN b.
Proof.
intros.
apply lt_suc_lteq in H0.
apply le_noteq_lt;assumption.
Qed.


Lemma lteqBN_suc: forall (a b:BN), a <=BN b -> (sucBN a) <=BN (sucBN b). 
Proof.
intros.
inversion H.
constructor.
apply lt_suc_lteq.
apply lt2.
trivial.
Qed.




(** >10 Axiomas de COPO para <BN*)

Theorem not_lt_suc: forall (a:BN), ~ exists (b:BN), a <BN b /\ b <BN (sucBN a).
Proof.
intros.
intro.
induction a.
+ destruct H.
  destruct H.
  - apply ltBN_aUZ in H0.
  rewrite H0 in H.
  inversion H.
+ apply IHa.
  destruct H.
  destruct H.
  simpl in H0.
  induction x.
  inversion H.
  - apply lt_U in H.
    inversion H0.
    -- subst.
        contradict H.
        apply ltBN_arefl.
    -- subst.
       contradict H3. 
       apply ltBN_asym.
       assumption.
  - inversion H0. subst.
    inversion H. subst.
    contradict H3.
    apply ltBN_arefl.
    subst. contradict H4.
    apply ltBN_asym.
    assumption.
+ apply IHa.
  destruct H.
  destruct H.
  apply le_ab_lt_asucb in H0.
  exfalso.
  apply (ltBN_arefl (D a)).
  eapply  lt_lteqBN_trans.
  apply H.
  assumption.
Qed. 


(** >E Concretar los casos faltantes este problema. Dificultad 4. Hint: los casos se parecen. *)
Lemma lt_trichotomy: forall (a b:BN), a <BN b \/ a=b \/ b <BN a.
Proof.
induction a, b.
- right. left. reflexivity.
- left. constructor.
- left. constructor.
- right. right. constructor.
- specialize IHa with b.
  destruct IHa.
  left. constructor. assumption.
  destruct H. right. left. rewrite H. reflexivity.
  right. right. constructor. assumption.
Admitted.

Lemma bbalCond_eqs: forall (s t:BN), t <=BN s -> s <=BN sucBN t -> s = t \/ s = sucBN t.  
Proof.
intros.
inversion H.
intuition.
inversion H0.
intuition.
exfalso.
eapply not_lt_suc.
exists s.
split.
exact H1.
assumption.
Qed.




(** >11 Propiedades de orden <BN respecto a pred *)

Lemma ltpred : forall (a:BN), a <> Z -> (predBN a) <BN a.
Proof.
intros.
induction a.
- contradict H. reflexivity.
- simpl. destruct a. 
  + constructor. 
  + apply ltBNDU. 
    apply IHa. 
    apply not_eq_sym.
    apply ZnotU.
  + apply ltBNDU.
    apply IHa.
    apply not_eq_sym.
    apply ZnotD. 
- simpl. apply ltBNUDeq.
Qed.

Hint Resolve ltpred: PNatDb.

Lemma lteqBN_suc_pred : forall (a b:BN), 
  a <> Z -> a <=BN (sucBN b) -> (predBN a) <=BN b.
Proof.
intros.
assert ((predBN a) <BN a).
apply ltpred.
trivial.
assert (predBN a <BN sucBN b).
eapply lt_lteqBN_trans.
eexact H1.
trivial.
apply lt1.
trivial.
Qed.

Hint Resolve lteqBN_suc_pred: PNatDb.


