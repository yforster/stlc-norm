(* 
Proof from the lecture Semantics (https://www.ps.uni-saarland.de/courses/sem-ws11/) by Gert Smolka.

Source: http://www.ps.uni-saarland.de/courses/sem-ws11/script/StlcTerm.html

Slightly adapted.
*)

Set Implicit Arguments.

Require Import Arith.
Tactic Notation "inv" hyp(A) := inversion A ; subst ; clear A.

Section Relation.
Variable X : Type.

Definition rel : Type := X -> X -> Prop.

Definition reducible (r : rel) (x : X) : Prop :=
exists y, r x y.

Definition normal (r : rel) (x : X) : Prop :=
~ reducible r x.

Definition reddec (r : rel) : Prop :=
forall x, reducible r x \/ normal r x.

Inductive star (r : rel) : rel :=
| starR x : star r x x
| starS x y z : r x y -> star r y z -> star r x z.

Inductive normalizes (r : rel) : X -> Prop :=
| normalizesI1 x : normal r x -> normalizes r x
| normalizesI2 x y : r x y -> normalizes r y -> normalizes r x.

Inductive terminates (r : rel) : X -> Prop :=
| terminatesI x : (forall y, r x y -> terminates r y) -> terminates r x.

Definition terminating (r : rel) : Prop :=
forall x, terminates r x.

Lemma reddec_terminates_normalizes r x :
reddec r -> terminates r x -> normalizes r x.

Proof. intros D T. induction T as [x _ IH].
destruct (D x) ; firstorder using normalizes. Qed.

End Relation.

Inductive var : Type :=
  varN : nat -> var.

Definition beq_var var1 var2 :=
  match (var1, var2) with (varN n1, varN n2) => beq_nat n1 n2 end.

Theorem beq_var_refl : forall i,
  true = beq_var i i.
Proof.
intros. destruct i. unfold beq_var. apply beq_nat_refl.
Qed.

Theorem not_eq_false_beq_var : forall i1 i2,
  i1 <> i2 -> false = beq_var i1 i2.
Proof.
intro. destruct i1 as [n1].
induction n1; destruct i2 as [n2]; destruct n2; unfold beq_var; intuition.
simpl. rewrite (IHn1 (varN n2)). trivial. intuition. inversion H0. intuition.
Qed.

Theorem beq_var_eq : forall x y, match (beq_var x y) with true => x = y | false => x <> y end.
intros [n] [m].
revert m. induction n.
intros [|m'].
simpl. reflexivity.
simpl. discriminate.
intros [|m'].
simpl. discriminate.
generalize (IHn m'). unfold beq_var. simpl.
destruct (beq_nat n m').
congruence.
intros H1 H2. inversion H2. apply H1. rewrite H0. reflexivity.
Qed.

Inductive ty : Type :=
  | tyX : ty
  | tyA : ty -> ty -> ty.

Inductive tm : Type :=
  | tmV : var -> tm
  | tmA : tm -> tm -> tm
  | tmL : var -> ty -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (tmL x T t).

Definition partial_map (A:Type) := var -> option A.
Definition sub : Type := partial_map tm.
Definition ctx : Type := partial_map ty.

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition update {A:Type} (Gamma : partial_map A) (x:var) (T : A) :=
  fun x' => if beq_var x x' then Some T else Gamma x'.

Definition drop {A:Type} (Gamma : partial_map A) (x:var) :=
  fun x' => if beq_var x x' then None else Gamma x'.


Inductive free : var -> tm -> Prop :=
  | freeV : forall x,
      free x (tmV x)
  | freeA1 : forall x t1 t2,
      free x t1 -> free x (tmA t1 t2)
  | freeA2 : forall x t1 t2,
      free x t2 -> free x (tmA t1 t2)
  | freeL : forall x y T11 t12,
        y <> x
     -> free x t12
     -> free x (tmL y T11 t12).


Definition closed (t:tm) :=
  forall x, ~ free x t.

Definition closed' (theta:sub) :=
  forall x s, theta x = Some s -> closed s.

Fixpoint simsubst (theta : sub) (t : tm) : tm :=
match t with
| tmV x => match theta x with Some s => s | None => t end
| tmA t1 t2 => tmA (simsubst theta t1) (simsubst theta t2)
| tmL x T t1 => tmL x T (simsubst (drop theta x) t1)
end.

Definition subst := fun (x:var) (s:tm) => simsubst (update empty x s).

Lemma simsubst_coin : forall t (theta theta':sub),
(forall x, free x t -> theta x = theta' x)
->
simsubst theta t = simsubst theta' t.
intros t. induction t; intros theta theta' H1; simpl.
rewrite <- (H1 v (freeV v)).
destruct (theta v); reflexivity.
rewrite (IHt1 theta theta'). rewrite (IHt2 theta theta'). reflexivity.
intros x H2. apply H1. eauto using free.
intros x H2. apply H1. eauto using free.
rewrite (IHt (drop theta v) (drop theta' v)). reflexivity.
intros x H2. unfold drop.
case_eq (beq_var v x).
reflexivity.
intros H3. apply H1. constructor. intros H4. rewrite H4 in H3. rewrite <- beq_var_refl in H3.
discriminate.
assumption.
Qed.


Lemma subst_id : forall t, simsubst empty t = t.
Proof with eauto.
assert (forall t theta, (forall x, theta x = None) -> simsubst theta t = t)...
induction t; intros...
simpl. rewrite H. reflexivity.
simpl. rewrite IHt1. rewrite IHt2... trivial.
simpl. rewrite IHt...
  intro x. unfold drop. destruct (beq_var v x)...
Qed.

Lemma subst_closed : forall t theta, closed t -> simsubst theta t = t.
intros t theta H.
rewrite <- subst_id.
rewrite (simsubst_coin empty theta).
reflexivity.
intros x H'. destruct (H x). assumption.
Qed.

Lemma subst_simsubst : forall (theta:sub) x s t, closed' theta ->
      subst x s (simsubst (drop theta x) t) = simsubst (update theta x s) t.
intros theta x s t.
revert theta. induction t; intros theta H0; simpl.
unfold update. unfold drop.
case_eq (beq_var x v).

intros H1. unfold subst. unfold update. simpl. rewrite H1. reflexivity.

intros H1. unfold subst.
rewrite (simsubst_coin (update empty x s) empty).
apply subst_id.
case_eq (theta v).
intros t H3.
intros y H2.
generalize (H0 v t H3). intros H4. destruct (H4 y H2).
intros H2 y H3. unfold update.
inv H3. rewrite H1. reflexivity.

unfold subst. simpl.
rewrite <- (IHt1 theta H0).
rewrite <- (IHt2 theta H0).
reflexivity.

unfold subst. simpl.
assert (H0':closed' (drop theta v)).
intros y u H2. unfold closed' in H0. apply (H0 y u). revert H2. unfold drop. destruct (beq_var v y).
discriminate. eauto.
generalize (IHt (drop theta v) H0').
unfold subst.
case_eq (beq_var v x); intros H1.

intros _.
rewrite (simsubst_coin (drop (update theta x s) v) (drop theta v)).
rewrite (simsubst_coin (drop (drop theta x) v) (drop theta v)).
rewrite (simsubst_coin (drop (update empty x s) v) empty).
rewrite subst_id. reflexivity.
intros y _. unfold update,drop. case_eq (beq_var v y); intros H2; case_eq (beq_var x y); intros H3; try reflexivity.
generalize (beq_var_eq v y). rewrite H2. intros H2'. destruct H2'.
generalize (beq_var_eq v x). rewrite H1. intros H1'. rewrite H1'.
generalize (beq_var_eq x y). rewrite H3. intros H3'. exact H3'.
intros y _. unfold drop. case_eq (beq_var v y); intros H2; case_eq (beq_var x y); intros H3; try reflexivity.
generalize (beq_var_eq v y). rewrite H2. intros H2'. destruct H2'.
generalize (beq_var_eq v x). rewrite H1. intros H1'. rewrite H1'.
generalize (beq_var_eq x y). rewrite H3. intros H3'. exact H3'.
intros y _. unfold update,drop. case_eq (beq_var v y); intros H2; case_eq (beq_var x y); intros H3; try reflexivity.
generalize (beq_var_eq v y). rewrite H2. intros H2'. destruct H2'.
generalize (beq_var_eq v x). rewrite H1. intros H1'. rewrite H1'.
generalize (beq_var_eq x y). rewrite H3. intros H3'. exact H3'.

rewrite (simsubst_coin (drop (update theta x s) v) (update (drop theta v) x s)).
rewrite (simsubst_coin (drop (drop theta x) v) (drop (drop theta v) x)).
rewrite (simsubst_coin (drop (update empty x s) v) (update empty x s)).
intros H2. rewrite H2. reflexivity.
intros y _. unfold update,drop. case_eq (beq_var v y); intros H2; case_eq (beq_var x y); intros H3; try reflexivity.
generalize (beq_var_eq v x). rewrite H1. intros H1'. destruct H1'.
generalize (beq_var_eq x y). rewrite H3. intros H3'. rewrite H3'.
generalize (beq_var_eq v y). rewrite H2. intros H2'. exact H2'.
intros y _. unfold drop. case_eq (beq_var v y); intros H2; case_eq (beq_var x y); intros H3; try reflexivity.
intros y _. unfold update,drop. case_eq (beq_var v y); intros H2; case_eq (beq_var x y); intros H3; try reflexivity.
generalize (beq_var_eq v x). rewrite H1. intros H1'. destruct H1'.
generalize (beq_var_eq x y). rewrite H3. intros H3'. rewrite H3'.
generalize (beq_var_eq v y). rewrite H2. intros H2'. exact H2'.
Qed.

Inductive step : tm -> tm -> Prop :=
  | stepB : forall x T t12 t2,
         step (tmA (tmL x T t12) t2) (subst x t2 t12)
  | stepA1 : forall t1 t1' t2,
         step t1 t1'
      -> step (tmA t1 t2) (tmA t1' t2)
  | stepA2 : forall t1 t2 t2',
         step t2 t2'
      -> step (tmA t1 t2) (tmA t1 t2').


Notation "t1 '==>' t2" := (step t1 t2) (at level 40).

Inductive type : ctx -> tm -> ty -> Prop :=
  | typeV : forall Gamma x T,
      Gamma x = Some T ->
      type Gamma (tmV x) T
  | typeL : forall Gamma x S T t,
      type (update Gamma x S) t T ->
      type Gamma (tmL x S t) (tyA S T)
  | typeA : forall S T Gamma t s,
      type Gamma t (tyA S T) ->
      type Gamma s S ->
      type Gamma (tmA t s) T.

Lemma type_inv : forall Gamma Gamma' t T,
   (forall x, free x t -> Gamma x = Gamma' x)
-> type Gamma t T -> type Gamma' t T.
intros Gamma Gamma' t T H1 H2. revert Gamma' H1. induction H2; intros Gamma' H1.
constructor. rewrite <- H1. assumption. constructor.
constructor. apply IHtype. intros y H3. unfold update.
case_eq (beq_var x y); intros H4. reflexivity. apply H1. constructor. generalize (beq_var_eq x y). rewrite H4. eauto.
assumption.
eauto 10 using type,free.
Qed.

Lemma free_in_context : forall x t T Gamma,
   free x t ->
   type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
intros. generalize dependent Gamma. generalize dependent T.
induction H; intros; try solve [inv H0; eauto].
inv H1. apply IHfree in H7.
unfold update in H7. apply not_eq_false_beq_var in H. rewrite <- H in H7...
Qed.

Lemma type_empty : forall t T,
 type empty t T -> forall Gamma, type Gamma t T.
intros t T H Gamma.
apply type_inv with (Gamma := empty).
intros x H'. destruct (free_in_context H' H) as [T' H''].
discriminate.
assumption.
Qed.


Lemma substitution_lemma' : forall Gamma t T theta Gamma',
               type Gamma t T ->
               (forall x S s, Gamma x = Some S -> theta x = Some s -> forall Gamma'', type Gamma'' s S) ->
               (forall x S, Gamma x = Some S -> theta x = None -> Gamma' x = Some S) ->
               type Gamma' (simsubst theta t) T.
Proof.
  intros Gamma t T theta Gamma' H. revert theta Gamma'. induction H; intros theta Gamma'.
  - intros H1 H2.
    simpl. case_eq (theta x).
    intros t H3. apply (H1 x); eauto.
    intros H3. econstructor. eapply H2. eassumption. eassumption.
  - intros H1 H2. simpl. constructor. apply IHtype.
    + intros y T' t'. unfold update,drop. case_eq (beq_var x y).
      discriminate.
      intros _. apply (H1 y).
    + intros y T'. unfold update,drop. case_eq (beq_var x y).
      eauto.
    intros _. apply (H2 y).
  - intros H1 H2. simpl. apply typeA with (S := S).
    eapply IHtype1. eassumption. eassumption.
    eauto.
Qed.

Lemma substitution_lemma : forall Gamma t T theta,
  type Gamma t T ->
  (forall x S, Gamma x = Some S -> exists s, theta x = Some s /\ type empty s S) ->
  type empty (simsubst theta t) T.
Proof.
intros Gamma t T theta H1 H2.
apply substitution_lemma' with (Gamma := Gamma) (theta := theta) (Gamma' := empty).
- assumption.
- intros x S s H3 H4. destruct (H2 x S H3) as [s' [H5 H6]].
  rewrite H4 in H5. inv H5. apply type_empty. assumption.
- intros x S H3 H4. destruct (H2 x S H3) as [s' [H5 H6]].
  rewrite H4 in H5. discriminate.
Qed.


Theorem preservation: forall t t' T,
  type empty t T -> t ==> t' -> type empty t' T.
Proof.
intros t t' T H1 H. revert T H1.
induction H.
intros T1 H1. inv H1. inv H3.
apply substitution_lemma with (Gamma := update empty x S) (t := t12) (T := T1) (theta := update empty x t2).
assumption.
intros y S'. unfold update. case (beq_var x y); intros H7.
exists t2. split. reflexivity. inv H7. assumption.
discriminate.
intros T H1. inv H1. econstructor. apply IHstep. eassumption. assumption.
intros T H1. inv H1. econstructor. eassumption. apply IHstep. assumption.
Qed.


Definition ter (t : tm) : Prop := terminates step t.


Fixpoint R (T:ty) (t:tm) {struct T} : Prop := type empty t T /\
  match T with
  | tyX => ter t
  | tyA T1 T2 => ter t /\ (forall s, R T1 s -> R T2 (tmA t s))
  end.


Definition R' (Gamma:ctx) (theta:sub) : Prop :=
(forall x S, Gamma x = Some S -> exists s, theta x = Some s /\ R S s)
/\
(forall x s, theta x = Some s -> exists S, Gamma x = Some S /\ R S s).


Lemma R_typed : forall T t,
  R T t -> type empty t T.
Proof.
intros. destruct T; simpl R in H; intuition.
Qed.


Lemma R_ter : forall T t,
  R T t -> ter t.
Proof.
intros. destruct T; simpl R in H; intuition.
Qed.

Lemma R_implies_closed': forall theta Gamma,
  R' Gamma theta -> closed' theta.
Proof.
unfold closed'. intros theta Gamma [H1 H2] x s H3. intros y H4.
destruct (H2 x s) as [S [Hc Hd]]. assumption.
assert (H5:type empty s S).
apply R_typed. assumption.
destruct (free_in_context H4 H5) as [T' H6].
inv H6.
Qed.

Lemma R_substitution_lemma : forall Gamma t T theta,
  type Gamma t T -> R' Gamma theta -> type empty (simsubst theta t) T.
Proof.
  intros Gamma t T theta H1 [H2 H3].
  apply substitution_lemma with (Gamma := Gamma).
  - assumption.
  - intros x S H4.
    destruct (H2 x S H4) as [s [H5 H6]].
    exists s. split.
    + assumption.
    + apply R_typed. assumption.
Qed.

Lemma R_preserving_context_update: forall Gamma theta T x t,
  R' Gamma theta ->
  R T t ->
  R' (update Gamma x T) (update theta x t).
Proof.
  unfold update. intros Gamma theta T x t [H0a H0b] H1. split.
  intros y S.
  case_eq (beq_var x y). intros H2 H3. exists t. split. reflexivity. inv H3. assumption.
  intros H2 H3. apply H0a. assumption.
  intros y s.
  case_eq (beq_var x y). intros H2 H3. exists T. split. reflexivity. inv H3. assumption.
  intros H2 H3. apply H0b. assumption.
Qed.

Lemma R_step_closed : forall T t t',
  t ==> t' -> R T t -> R T t'.
intros T; induction T; intros t.
intros t' H2 H3. inv H3. inv H0. split.
apply preservation with (t:=t); assumption.
exact (H1 t' H2).

intros t' H2 [H3 [H4 H5]]. fold R in H5. split.
eapply preservation; eassumption.
split.
inv H4. exact (H t' H2).
intros s H6. generalize (H5 s H6).
apply (IHT2 (tmA t s) (tmA t' s)).
constructor. assumption.

Qed.

Definition E (T : ty) (t :tm) : Prop := forall t', t ==> t' -> R T t'.

Lemma R_term_ap : forall S T t,
  (forall u, type empty u T -> ~value u -> E T u -> R T u) ->
  type empty t (tyA S T) ->
  ~value t ->
  E (tyA S T) t ->
  forall s, R S s -> R T (tmA t s).
Proof.  
  intros S T t H0 H1 H2 H3 s H4. generalize (R_ter S s H4). intros H. revert H4.
  unfold ter in H. 
  induction H as [s H IH].
  intros H4. apply H0.
  - econstructor. eassumption. apply R_typed. assumption.
  - intros H5. inv H5.
  - intros u H5. inv H5.
    + destruct H2. constructor.
    + destruct (H3 t1' H9) as [H3a [H3b H3c]].
      apply H3c. assumption.
    + apply (IH t2' H9).
      eapply R_step_closed. eassumption. assumption.
Qed.

Lemma R_exp_closed : forall T t, type empty t T ->
  ~value t ->
  E T t -> R T t.
Proof.
  induction T.
  - intros t H1 H2 H3.
  split. assumption. constructor. intros t' H4. apply R_ter with (T := tyX).
  apply H3. assumption.
  - intros t H1 H2 H3. simpl. do 2 (try split).
    + assumption.
    + unfold E in H3. constructor. intros t' H4. apply R_ter with (T := (tyA T1 T2)).
      apply H3. assumption.
    + intros s H4. apply (R_term_ap IHT2 H1 H2 H3).
      assumption.
Qed.

Lemma R_beta : forall S T x t, type (update empty x S) t T ->
  (forall s, R S s -> R T (subst x s t)) ->
  forall s, R S s -> R T (tmA (tmL x S t) s).
Proof.
  intros S T x t H0 H1 s H2. generalize (R_ter S s H2). intros H. revert H2. induction H. intros H3.
  apply R_exp_closed.
  - econstructor. 
    + econstructor. assumption. 
    + apply R_typed. assumption.
  - intros H4. inv H4.
  - intros t' H4. inv H4.
  apply H1. assumption.
  inv H8.
  apply H2. assumption. apply R_step_closed with (t := x0); assumption.
Qed.



Lemma Basic_lemma : forall Gamma t T theta,
  type Gamma t T -> R' Gamma theta -> R T (simsubst theta t).
Proof.
  intros Gamma t T theta H. revert theta. induction H; intros.
  - apply H0 in H. destruct H. destruct H. simpl. rewrite H. assumption.
  - assert (B:type empty (simsubst theta (tmL x S t)) (tyA S T)). {
      apply R_substitution_lemma with (Gamma := Gamma). constructor. assumption. assumption.
    }
    do 2 (try split).
    + exact B.
    + constructor. intros t' H'. inv H'.
    + intros s H1.
      apply R_beta; fold simsubst.
      * inv B. exact H4.
      * intros u H2. rewrite subst_simsubst. apply IHtype.
        apply R_preserving_context_update; assumption.
        apply R_implies_closed' with (Gamma := Gamma). assumption.
      * assumption.
  - simpl. generalize (IHtype1 theta H1); intros IH1. generalize (IHtype2 theta H1); intros IH2.
    destruct IH1 as [_ [_ IH1a]]. fold R in IH1a. apply IH1a. assumption.
Qed.


Theorem ter_step : forall t T,
  type empty t T -> ter t.
Proof.
intros t T H. apply R_ter with (T:=T).
rewrite <- (subst_id t).
apply Basic_lemma with (Gamma:=empty).
assumption.
split.
intros x S H1. inv H1.
intros x s H1. inv H1.
Qed.


Lemma reddec_step : reddec step.
intros s. induction s. right. intros [t H]. inv H.
assert (A:(exists x, exists S, exists s3, s1 = tmL x S s3) \/ ~ (exists x, exists S, exists s3, s1 = tmL x S s3)).
destruct s1.
right. intros [x [S [s3 H']]]. inv H'.
right. intros [x [S [s3 H']]]. inv H'.
left. exists v. exists t. exists s1. reflexivity.
destruct A as [[x [S [s3 A1]]]|A2].
rewrite A1. left. exists (subst x s2 s3). constructor.
destruct IHs1 as [[t1 H1]|H1].
left. exists (tmA t1 s2). constructor. assumption.
destruct IHs2 as [[t2 H2]|H2].
left. exists (tmA s1 t2). constructor. assumption.
right. intros [t H3]. inv H3.
apply A2. exists x. exists T. exists t12. reflexivity.
apply H1. exists t1'. assumption.
apply H2. exists t2'. assumption.
right. intros [t' H]. inv H.
Qed.

Lemma norm_step : forall t T, type empty t T -> normalizes step t.
intros t T H. apply reddec_terminates_normalizes.
apply reddec_step.
apply ter_step with (T:=T). assumption.
Qed.

Lemma progress : forall t T, type empty t T -> value t \/ exists t', step t t'.
intros t. induction t as [x|t1 IHt1 t2 IHt2|x T1 t1 IHt1]; simpl; intros T H1.
inv H1. discriminate.
inv H1.
destruct (IHt1 _ H3) as [H4|[t1' H4]].
destruct (IHt2 _ H5) as [H6|[t2' H6]].
inv H4. right. exists (subst x t2 t). constructor.
right. exists (tmA t1 t2'). constructor. assumption.
right. exists (tmA t1' t2). constructor. assumption.
left. constructor.
Qed.

Lemma norm_step_val : forall t T, type empty t T -> exists t', value t' /\ star step t t'.
intros t T H.
assert (A:normalizes step t).
exact (norm_step H).
induction A.
exists x. split. destruct (progress H). assumption. destruct H1. destruct H0. exists x0. assumption.
eauto using star.
assert (B:type empty y T).
apply preservation with (t := x); assumption.
destruct (IHA B) as [t' [H1 H2]].
exists t'. split. assumption. econstructor. eassumption. assumption.
Qed.
