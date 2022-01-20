(** Semántica y verificación 22-1
  
  Funciones de adición y remosión de cabeza
  
  Ver a los árboles de Braun como listas incita a definir funciones
  que remuevan eficientemente su primer y ´ultimo elemento de los árboles. 
  La estructura de los árboles de Braun permite de esta cualidad. 
  En este script definimos las funciones de remosión y adición
  del primer y ´ultimo elemento del  árbol de Braun.
  A la adición de elementos se le llama extension, donde
  para el primer elemento lo llamamos hight-extension (he) 
  y el ´ultimo elemento low-extension (le).
  La remosión de elementos se llama removal y análogamente se tiene
  high-removal (hr) y low-removal (lr).

  Este script fue basado de los cursos de Favio Ezquiel
  Miranda Perea y modificado en ciertos aspectos.
  
  Edición por Luis Felipe Benítez Lluis

  Contenido:
    1 Definición de lookup y opdate
    2 Propiedades de seguridad de consulta y actualización
        
        
    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. *)



From Proyecto02Base Require Import bintree.
From Proyecto02Base Require Import binnat.
From Proyecto02Base Require Import order_binnat.
From Proyecto02Base Require Import braunT.
From Proyecto02Base Require Import lookup_BT.



(** >1 Definiciones de extensión y remosión de*)

Fixpoint le (x:A) (t:BTree) : BTree :=
 match t with
    E => N x E E
  | N y s t => N x (le y t) s
 end.


 
Fixpoint lr (t:BTree) : BTree :=
 match t with
  | E => undefBTree
  | N x l r => match l with
               | E => E
               | N y _ _ => N y r (lr l)
               end
 end.

(** >E Rellenar esta definición. Dificultad 2*)
Fixpoint he (x:A) (t:BTree) : BTree  . Admitted.
 

Fixpoint hr (t:BTree) : BTree  :=
 match t with
  | E => undefBTree
  | N x l r => match l with 
               | E => E
               | _ => match bsize t with 
                      | U b => N x l (hr r)
                      | D b => N x (hr l) r
                      |   Z => undefBTree 
                      end
               end
 end.
 
 
 

(** >2 Propiedades de Low Extension le *)

Lemma le_head: forall (t: BTree) (x:A),  
  lookup_bn (le x t) Z = x.
Proof.
intros.
destruct t.
- intuition.
- intuition.
Qed.

Lemma le_hasroot: forall (a:A)(t:BTree), 
    exists (t1 t2:BTree),
    (le a t)= N a t1 t2.
Proof.    
intros.
induction t.
- exists E. exists E. simpl. reflexivity.
- simpl. exists (le a0 t2). exists t1.
  reflexivity.
Qed.

Lemma bsize_le: forall (t:BTree) (x:A), 
  bsize (le x t) = sucBN (bsize t).
Proof.
intro.
assert (HBal := allBal t).  
induction HBal.
- reflexivity.
- intro.
  simpl.
  rewrite IHHBal2.
  rewrite <- plusSuc_l.
  rewrite plusComm.
  reflexivity.
Qed.

Lemma bal_le: forall (t:BTree), bbal t -> 
                 forall (x:A), bbal (le x t).
Proof.
intros t HtBal.
induction HtBal.
- simpl.
  apply bbal_leaf.
- intros.
  simpl.
  constructor.
  + apply IHHtBal2.
  + assumption.
  + rewrite bsize_le.
    assumption.
  + rewrite bsize_le.
    apply lteqBN_suc.
    assumption.
Qed.

Lemma le_idx: forall (t:BTree),  
  bbal t -> 
  forall (j:BN), j <BN (bsize t) -> 
  forall (x:A), lookup_bn (le x t) (sucBN j) = lookup_bn t j.
Proof.
intros t B.
induction B.
- intros.
  simpl in H.
  inversion H.
- intros.
  clear IHB1.
  destruct j.
  + simpl.
    apply le_head.
  + reflexivity.
  + simpl.
    apply IHB2.
    apply (lt_D_bsize j a s t).
    assumption.
Qed.


(** >3 Propiedades de High Extension*)

Lemma he_hasroot: forall (a:A)(t:BTree), 
    exists (y:A)(t1 t2:BTree),
    (he a t)= N y t1 t2.
Proof.
intros.
induction t.
- simpl. exists a. exists E. exists E. reflexivity.
- simpl.
  pose proof SucBNisUorD (bsize t1 +_ bsize t2).
  destruct H. destruct H.
  + rewrite H.
    destruct IHt1. destruct H0. 
    destruct H0.
    exists a0. exists (he a t1). exists t2.
    reflexivity.
  + rewrite H.
    exists a0. exists t1. exists (he a t2).
    reflexivity.
Qed.


(** >E Rellenar este problema. Dificultad 3. 
Hint: se puede desestructurar expresiones de acuerdo a su definición. 
Ejemplo :destruct (bbal_size_r a t1 t2).*)
Lemma bsize_he: forall (t:BTree) (x:A), 
                    bsize (he x t) = sucBN (bsize t).
Proof.
Admitted.

(** >E Finalizar el caso restante a este problema. Dificultad 4. *)
Lemma bal_he: forall (t:BTree), bbal t -> 
                forall (x:A), bbal (he x t).
Proof.
intros t Ht.
induction t.
- simpl.
  apply bbal_leaf.
- intros.
  inversion Ht.
  subst.
  destruct (bbal_size_r a t1 t2).
  + assert(H6:=H).
    apply size_caseU in H.
    simpl in H6.
    simpl.
    rewrite H6.
    constructor.
    * apply IHt1.
      assumption.
    * assumption.
    * rewrite bsize_he.
      inversion H4.
      -- intuition.
      -- eapply lteqBN_trans.
         ++ apply H4.
         ++ apply lteqs.
    * rewrite bsize_he.
      rewrite H.
      intuition.
  + 
Admitted.

Lemma he_last: forall (t: BTree) (x:A),  
    lookup_bn (he x t) (bsize t) = x.
Proof.
intros.
pose proof (allBal t).
induction t.
+ simpl. reflexivity.
+ destruct (bbal_size_r a t1 t2).
  ++  simpl. simpl in H0.
      rewrite H0.
      inversion H.
      subst.
      simpl.
      apply (prop_0_U a t1 t2 (bsize t2)) in H.
      - destruct H.
        rewrite <-H.
        apply IHt1.
        assumption.
      - assumption.
  ++ simpl. simpl in H0.
      rewrite H0.
      simpl. apply IHt2.
      inversion H.
      assumption.
Qed.
     
Lemma he_idx: forall (t:BTree),  
  bbal t -> 
  forall (j:BN), j <BN (bsize t) -> 
  forall (x:A), lookup_bn (he x t) j = lookup_bn t j.
Proof.
intro.
intro.
induction t.
- intros. simpl.
  inversion H0.
- intros. 
  destruct (bbal_size_r a t1 t2).
  + simpl. 
    simpl in H1.
    rewrite H1.
    simpl.
    destruct j as [  |  a0 | b0].
    * reflexivity.
    * simpl in H0.
      rewrite H1 in H0.
      inversion H0.
      inversion H.
      subst.
      apply IHt1.
      assumption.
      apply (prop_0_U a t1 t2 (bsize t2)) in H1.
      destruct H1.
      rewrite H1.
      assumption.
      assumption.
    * reflexivity.
  + simpl in H1.
    simpl. rewrite H1.
    simpl.
    destruct j as [  |  a0 | b0].
    * reflexivity.
    * reflexivity.
    * simpl in H0.
      rewrite H1 in H0.
      inversion H0.
      inversion H.
      subst.
      apply IHt2.
      ** assumption.
      ** assumption.
Qed.      





(** >4 Propiedades de Low-Removal lr*)

Proposition bsize_lr_pred_bsize:
  forall (t:BTree), t<>E ->
    bsize (lr t) = predBN (bsize t).
Proof.
intros.
pose proof (allBal t).
induction t as [| a l IHl r].
- contradict H. reflexivity.
- inversion H0.
  subst.
  simpl (predBN (bsize (N a l r))).
  rewrite predsucBNinv.
  destruct l. 
    + apply leftE_leaf in H0.
       rewrite H0.
       simpl.
       reflexivity.
       reflexivity.
    + simpl (bsize (lr (N a (N a0 l1 l2) r))).
       simpl in IHl.
       rewrite IHl.
       3: assumption.
       2: intro W1; inversion W1.
       rewrite plusSuc_r.
       rewrite predsucBNinv.
       simpl.
       rewrite plusComm.
       reflexivity.
Qed.       
  
Proposition bbal_bbal_lr:
  forall (t:BTree), t<> E->
    bbal t -> bbal (lr t).
Proof.
intros.
induction t as [| a l IHl r].
- contradict H; reflexivity.
- inversion H0.
  subst.
  destruct l.
  + apply leftE_leaf in H0.
    2: reflexivity.
    rewrite H0.
    simpl.
    constructor.
  + apply bbalN. 
    ++ assumption.
    ++ apply IHl.
       intro W; inversion W.
       assumption.
       
    ++ fold lr. 
       apply lteqBN_suc_pred in H7.
       rewrite <- bsize_lr_pred_bsize in H7.
       simpl in H7.
       assumption.
       intro W; inversion W.
       apply bsize_nonZ.
       intro W; inversion W.
    ++ fold lr. 
       assert ( 
        sucBN (predBN (bsize (N a0 l1 l2)))
         = bsize (N a0 l1 l2)) as W.
        { apply  sucpredBNinv. 
         apply bsize_nonZ.
         intro W; inversion W. }
        rewrite <- bsize_lr_pred_bsize in W.
        rewrite <- W in H6.
    simpl ( lr (N a (N a0 l1 l2) r)).
    exact H6. 
    intro W0; inversion W0.
Qed.
    

Proposition lkp_lr_lkp_suc:
  forall (t:BTree)(j:BN), t<> E -> j <BN bsize (lr t) ->
    lookup_bn (lr t) j = lookup_bn t (sucBN j) .
Proof.
intros.
generalize dependent j.
pose proof (allBal t) as B.
induction t as [| a l IHl r].
(* base *)
intros.
contradict H; reflexivity.
+ intros j J.
  destruct  l.
  ++ apply leftE_leaf in B.
     2: reflexivity.
     rewrite B in J.
     simpl in J.
     inversion J.
  ++  remember (N a0 l1 l2) as l.
      destruct j.
      - rewrite Heql.
        simpl.
        reflexivity.
      - rewrite Heql.
        simpl.
        reflexivity.
      - rewrite Heql in IHl.
        remember (bsize (lr (N a0 l1 l2))) as s.
        simpl  in IHl.
        rewrite Heql.
        simpl (lookup_bn (lr (N a (N a0 l1 l2) r)) (D j)).
        rewrite IHl.
        reflexivity.
        -- intro X; inversion X.
        -- inversion B.
           rewrite <- Heql.
           assumption.
        -- rewrite bsize_lr_pred_bsize in J.
           2: intro X; inversion X.
           simpl in J.
           rewrite predsucBNinv in J. 
       simpl.
       rewrite Heqs.
       rewrite <-Heql.
       rewrite bsize_lr_pred_bsize.
       (* esta meta sale sin deestructuración pero
          requiere lemas del orden en la suma*)
       assert (bsize l <> Z ) as A1.
       { rewrite Heql.
         simpl.
         apply not_eq_sym.
         apply ZnotSucBN. }
       assert (l<>E) as A2.
       { rewrite Heql.
         intro X; inversion X.
        }
       clear IHl IHr Heqs.
       destruct (bbal_size_r a l r).
       3: { rewrite Heql.
            intro X; inversion X. }
       {  
         apply (size_caseU a l r (bsize r)) in H0 as W.
         rewrite <- W in J.
         rewrite <-( sucpredBNinv (bsize l)) in J.
       2: assumption.
       rewrite <-plusSuc_r in J.
       rewrite plus_D in J.
       inversion J.
       assumption. }
       { 
         apply (size_caseD a l r (bsize r)) in H0 as W.
         rewrite W.
         rewrite predsucBNinv.
         rewrite W in J.
         rewrite <- plusSuc_l in J.
         rewrite plus_U in J.
         inversion J.
         assumption. }
Qed.

(* Inversión entre lr y le*)
Proposition lr_le_inv:
  forall (t:BTree)(x:A),
    lr (le x t) = t.
Proof.
intro.
induction t.
simpl. reflexivity.
intros.
simpl (le x (N a t1 t2)).
simpl.
pose proof (le_hasroot a t2).
rewrite IHt2.
destruct H.
destruct H.
rewrite H.
reflexivity.
Qed.

Proposition le_lkp_lr_inv:
  forall (t:BTree), t<> E ->
    le (lookup_bn t Z) (lr t)=t.
Proof.
intros.
pose proof (allBal t).
induction t as [| a l IHl r].
contradict H.
reflexivity.
simpl.
destruct l.
- simpl. 
  apply leftE_leaf in H0.
  2: reflexivity.
  rewrite H0.
  reflexivity.
- inversion H0.
  subst.
  simpl (le a (N a0 r (lr (N a0 l1 l2)))).
  rewrite <-IHl.
  simpl.
  reflexivity.
  intro W; inversion W.
  assumption.
Qed.





(** >5 Propiedades de High-Removal hr*)

Proposition bsize_hr_pred_bsize:
  forall (t:BTree), t<> E ->
    bsize (hr t)= predBN (bsize t).
Proof.
intros.
pose proof (allBal t).
induction t as [| a l IHl r].
contradict H. reflexivity.
inversion H0.
subst.
simpl (predBN (bsize (N a l r))).
rewrite predsucBNinv.
destruct (bbal_size_r a l r).
+ apply (size_caseU a l r (bsize r)) in H1 as W.
  simpl.
  simpl in H1.
  rewrite H1.
  destruct l.
  ++ rewrite <-W.
     simpl.
     reflexivity.
  ++ simpl (bsize (N a (N a0 l1 l2) (hr r))).
     assert (r<>E) as NE. {
     apply <-bsize_nonZ.
     rewrite <-W.
     simpl.
     apply not_eq_sym.
     apply  ZnotSucBN. }
     rewrite IHr.
     
     rewrite plusSuc_r.
     rewrite sucpredBNinv.
     reflexivity.
     apply bsize_nonZ.
     assumption.
     assumption.
     assumption.
+ apply (size_caseD a l r (bsize r)) in H1 as W.
  simpl.
  simpl in H1.
  rewrite H1.
  destruct l.
  ++ simpl in W. 
     contradict W.
     apply ZnotSucBN.
  ++ 
     simpl (bsize (N a (hr (N a0 l1 l2)) r)).
     simpl in IHl.
     rewrite IHl.
     rewrite predsucBNinv.
     simpl.
     rewrite plusSuc_l.
     reflexivity.
     intro w;inversion w.
     assumption.
Qed.     

Proposition bbal_bbal_hr:
  forall (t:BTree), t<>E->
    bbal t -> bbal (hr t).
Proof.
intros.
induction t as [| a l IHl r].
contradict H; reflexivity.
destruct (bbal_size_r a l r).
- simpl.
  apply (size_caseU a l r (bsize r)) in H1 as W.
  simpl in H1.
  rewrite H1.
  inversion H0.
     subst.
  destruct l.
  -- constructor.
  -- assert (r<> E) as Q.
     {
     apply bsize_nonZ.
     rewrite <-W.
     simpl.
     apply not_eq_sym.
     apply  ZnotSucBN. }
     constructor.
     assumption.
     apply IHr.
     apply Q.
     assumption.

     + rewrite bsize_hr_pred_bsize.
       rewrite <- W.
       simpl.
       rewrite predsucBNinv.
       apply lteqs.
       assumption.
     + rewrite bsize_hr_pred_bsize.
       rewrite W.
       rewrite sucpredBNinv.
       constructor.
       apply bsize_nonZ.
       assumption.
       assumption .
- simpl.
  simpl in H1.
  rewrite H1.
  inversion H0.
  subst.
  apply size_caseD in H1.
  destruct l.
  constructor.
  2: apply a.
  constructor.
  apply IHl.
  intro w; inversion w.
  assumption.
  assumption.
  + rewrite bsize_hr_pred_bsize.
    2: intro w; inversion w.
    rewrite H1.
    rewrite predsucBNinv.
    constructor.
  + rewrite bsize_hr_pred_bsize.
     2: intro w; inversion w.
     rewrite H1.
     rewrite predsucBNinv.
     apply lteqs.
Qed.

Proposition lkp_hr_lkp:
  forall (t:BTree)(j:BN),t<>E-> j<BN bsize (hr t)->
    lookup_bn (hr t) j = lookup_bn t j.
Proof.
intros.
generalize dependent j.
pose proof (allBal t) as B.
induction t as [| a l IHl r].
(* base *)
contradict H; reflexivity.
(* inductivo*)
destruct (bbal_size_r a l r).
+ apply (size_caseU a l r (bsize r)) in H0 as W.
  simpl; simpl in H0.
  rewrite H0.
  destruct l.
  - intros j J.
    simpl in J.
    inversion J.
  - remember (N a0 l1 l2) as l.
    assert (r<>E) as X. {
     rewrite Heql in W.
     apply bsize_nonZ.
     rewrite <-W.
     simpl.
     apply not_eq_sym.
     apply  ZnotSucBN. }
     
    intros j J.
    rewrite Heql.
    simpl.
    destruct j.
      * reflexivity.
      * reflexivity.
      * rewrite IHr.
        reflexivity.
        exact X.
        inversion B.
        assumption.
       simpl in J.
       rewrite W in J.
       rewrite <- (sucpredBNinv (bsize r))in J.
(*        rewrite <- plusSuc in J. *)
       rewrite bsize_hr_pred_bsize in J.
       rewrite plus_D in J.
       inversion J.
       rewrite bsize_hr_pred_bsize.
       assumption.
       exact X.
       exact X.
       rewrite <-bsize_nonZ.
       exact X.
+   
  apply (size_caseD a l r (bsize r)) in H0 as W.
  simpl; simpl in H0.
  rewrite H0.
  destruct l.
  - intros j J.
    simpl in J.
    inversion J.
  - intros j J.
    
    (* remember (N a0 l1 l2) as l .*)
    destruct j.
      * simpl.  
       reflexivity.
      * rewrite <- IHl.
        -- simpl. reflexivity.
        -- intro S; inversion S.
        -- inversion B; assumption.
        -- remember (N a0 l1 l2) as l .
           simpl in J.
           rewrite bsize_hr_pred_bsize in J.
           rewrite <- (predsucBNinv (bsize r))in J.
           rewrite <- W in J.
           rewrite plus_U in J.
           inversion J.
           rewrite bsize_hr_pred_bsize.
           assumption.
           ++ rewrite Heql.
              intro X. discriminate X.
           ++ rewrite Heql.
              intro X. discriminate X.
              
      * simpl. reflexivity.
Qed.

Proposition hr_he_inv:
  forall (t:BTree)(x:A),
    hr (he x t)=t.
Proof.
intros.
simpl.
induction t as [| a l IHl r].
simpl. reflexivity.
intros.
destruct (bbal_size_r a l r).
- simpl. simpl in H.
  rewrite H.
  simpl.
  pose proof (he_hasroot x l).
  destruct H0.
  destruct H0.
  destruct H0.
  rewrite H0.
  rewrite <- H0.
  rewrite bsize_he.
  rewrite <- plusSuc_l.
  rewrite H.
  simpl.
  rewrite IHl.
  reflexivity.
- simpl. simpl in H.
  rewrite H.
  simpl.
  pose proof (he_hasroot x r).
  destruct H0.
  destruct H0.
  destruct H0.
  rewrite H0.
  rewrite <- H0.
  rewrite bsize_he.
  rewrite <- plusSuc_r.
  rewrite H.
  simpl.
  rewrite IHr.
  
  pose proof (allBal (N a l r)) as W.
  inversion W.
  subst.
  destruct l.
  apply leftE_leaf in W.
  2: reflexivity.
  2: reflexivity.
   rewrite W in H.
   simpl in H.
   discriminate H.
Qed.


Proposition he_lkp_pred_bsize_hr_inv:
  forall (t:BTree), t<>E->
    he(lookup_bn t (predBN (bsize t))) (hr t)=t.
Proof.
intros.
pose proof (allBal t) as B.
induction t as [| a l IHl r].
contradict H; reflexivity.

destruct (bbal_size_r a l r).
+ apply (size_caseU a l r (bsize r)) in H0 as W.
  destruct l.
  ++  simpl in H0.
  simpl.
  rewrite predsucBNinv.
(*   rewrite H0. *)
  rewrite <-W.
  simpl.
  simpl in W.
  symmetry in W.
  apply bsize_Z in W.
  rewrite W.
  reflexivity.
  ++ remember (N a0 l1 l2) as l.
    assert (bsize r<>Z) as A1.
    {
     rewrite <-W.
    rewrite Heql.
    simpl.
    apply not_eq_sym.
    apply ZnotSucBN.
    }
    assert (r<>E) as A2.
    { apply bsize_nonZ; assumption . }
    assert (bsize l +_ bsize r = D(predBN (bsize r))).
    { 
    rewrite <- predBNUD.
    rewrite <-H0.
    simpl.
    rewrite predsucBNinv.
    reflexivity.
    assumption.
    }
    simpl.
    rewrite predsucBNinv.
    rewrite H1.
    rewrite <- H1.
    simpl in H0.
    rewrite H0.
    rewrite Heql.
    rewrite <- Heql.
    simpl.
    rewrite bsize_hr_pred_bsize.
    rewrite plusSuc_r.
    rewrite sucpredBNinv.
    rewrite H1.
    rewrite IHr.
    reflexivity.
    assumption.
    inversion B.
    assumption.
    assumption.
    assumption.
+ apply (size_caseD a l r (bsize r)) in H0 as W.
  destruct l.
  ++  simpl in H0.
      apply leftE_leaf in B.
      2: reflexivity.
      rewrite B in W.
      simpl in W.
      inversion W.
  ++ remember (N a0 l1 l2) as l.
    assert (bsize l<>Z) as A1.
    {
    rewrite W.
    apply not_eq_sym.
    apply ZnotSucBN.
    }
    assert (l<>E) as A2.
    { apply bsize_nonZ; assumption . }
     assert (bsize l +_ bsize r = U(predBN (bsize l))) as J.
    {
    rewrite W.
    rewrite <-plusSuc_l.
    rewrite predsucBNinv.
    apply  plus_U.
    }
    simpl.
    rewrite predsucBNinv.
    rewrite J.
    rewrite Heql.
    rewrite <- Heql.
    simpl (sucBN (U (predBN (bsize l)))).
    remember (he (lookup_bn l (predBN (bsize l)))) as s.
    
    simpl.
    rewrite Heqs. rewrite Heqs in IHl.
    simpl.
    rewrite bsize_hr_pred_bsize.
    rewrite plusSuc_l.
    rewrite sucpredBNinv.
    rewrite J.
    rewrite IHl.
    reflexivity.
    assumption.
    inversion B.
    assumption.
    assumption.
    assumption.
Qed.

      