(**
  Defines a formally verified function for remove ambiguous non-unique values
  from a dataset. If you want to remove duplicate or "similar" values from
  a dataset, use the function defined in this module.
*)
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Open Scope list_scope.

Module List_aux.
  Definition Forall2_forall
    :  forall {A B : Type} (P : A -> B -> Prop) (xs : list A) (ys : list B) (H : Forall2 P xs ys),
       forall x, In x xs -> (exists y, In y ys /\ P x y).
  Proof. refine (
    fun A B P xs ys H =>
      Forall2_ind (fun xs' ys' => forall x, In x xs' -> (exists y, In y ys' /\ P x y)) 
        (fun x Hx_nil => False_ind _ Hx_nil)
        (fun x0 y0 xs' ys' Hxy Hxs_ys F x Hx_xs =>
          match Hx_xs with
          | or_introl Hx0_x =>
            ex_intro _ y0 _ (* See: base case *)
          | or_intror Hx_xs' =>
            let (y, Hy) := F x Hx_xs' in
            ex_intro _ y _ (* See: recurse *)
          end)
        H).

    (* II. footnote proofs. *)
    + split; [left; reflexivity|rewrite <- Hx0_x; exact Hxy]. 
    + split; [right; exact (proj1 Hy)|exact (proj2 Hy)].
  Qed.

  Definition Forall2_forall_r
    :  forall {A B : Type} (P : A -> B -> Prop) (xs : list A) (ys : list B) (H : Forall2 P xs ys),
       forall y, In y ys -> (exists x, In x xs /\ P x y).
  Proof. refine (
    fun A B P xs ys H =>
      Forall2_ind (fun xs' ys' => forall y, In y ys' -> (exists x, In x xs' /\ P x y)) 
        (fun x Hx_nil => False_ind _ Hx_nil)
        (fun x0 y0 xs' ys' Hxy Hxs_ys F y Hy_ys =>
          match Hy_ys with
          | or_introl Hy0_y =>
            ex_intro _ x0 _ (* See: base case *)
          | or_intror Hy_ys' =>
            let (x, Hx) := F y Hy_ys' in
            ex_intro _ x _ (* See: recurse *)
          end)
        H).

    (* II. footnote proofs. *)
    + split; [left; reflexivity|rewrite <- Hy0_y; exact Hxy]. 
    + split; [right; exact (proj1 Hx)|exact (proj2 Hx)].
  Qed.

  (* xs contains ys *)
  Definition sublist {A : Set} (xs ys : list A) : Prop :=
    forall y, In y ys -> In y xs.

  Lemma sublist_refl
    : forall {A : Set} (xs : list A), sublist xs xs.
  Proof.
    intros A xs x Hx. exact Hx.
  Qed.

  Lemma sublist_nil
    : forall {A : Set} xs, sublist (A := A) xs nil.
  Proof.
    intro A; induction xs; [unfold sublist|intro y]; contradiction.
  Qed.

  Lemma sublist_cons_nil
    : forall {A : Set} (xs : list A) (x : A), ~ sublist nil (x :: xs).
  Proof.
    intros A xs x H; exact (H x (or_introl (eq_refl _))).
  Qed.

  Lemma sublist_cons
    : forall {A : Set} (xs ys : list A) (x : A), sublist xs ys -> sublist (x :: xs) ys.
  Proof.
    intros A xs ys x H y Hy; right; exact (H y Hy).
  Qed.

  (**
    Proves that if an element is in a list but does not equal the first element, it
    must be in the tail of the list.
  *)
  Lemma in_tl {A} {xs : list A} {x y : A} (Hxy : x <> y) (Hy_xxs : In y (x :: xs)) : In y xs.
  Proof.
    induction Hy_xxs as [Hcontr|H]; [contradiction Hxy|assumption].
  Qed.

  Lemma existsb_forallb {A : Type} (f : A -> bool)
    :  forall (xs : list A), forallb (fun x => negb (f x)) xs = negb (existsb f xs).
  Proof.
    induction xs as [|x xs Hxs]; [reflexivity|].
    simpl; destruct (f x); simpl; [reflexivity|exact Hxs].
  Qed.

  Lemma negb_existsb {A : Type} (f : A -> bool) (xs : list A)
    :  negb (existsb f xs) = true <-> forall x : A, In x xs -> f x = false.
  Proof.
    split.
    + intro H; rewrite <- (existsb_forallb _ _) in H; set (H0 := proj1 (forallb_forall _ _) H).
      intros x Hx; destruct (f x) eqn:Hfx; [|reflexivity].
      set (Hcontr := (H0 x Hx)); simpl in Hcontr; rewrite Hfx in Hcontr; contradict Hcontr; discriminate.
    + intro H; rewrite <- (existsb_forallb _ _); apply (proj2 (forallb_forall _ _)); 
        intros x Hx; rewrite (H x Hx); reflexivity.
  Qed.

End List_aux.

Module Type T.
  Parameter t : Set.
End T.

Module Prod_t (A B : T).
  Definition t := (A.t * B.t)%type.
End Prod_t.

(** Represents types that can be compared using non-transitive equivalence. *)
Module Type Same (M : T).
  (* represents the list element comparator. *)
  Parameter is_same : M.t -> M.t -> bool.

  (* asserts that the comparator is reflexive. *)
  Axiom is_same_refl : forall x, is_same x x = true.

  (* asserts that the comparator is symmatric. *)
  Axiom is_same_sym : forall x y, is_same x y = is_same y x.
End Same.

Module Same_prod (A B : T) (A_same : Same A) (B_same : Same B).
   Module P := Prod_t A B.

  Open Scope bool_scope.

  Definition is_same x y :=
    match x, y with
    | (x0, x1), (y0, y1) =>
      A_same.is_same x0 y0 &&
      B_same.is_same x1 y1
    end.

  Lemma is_same_refl : forall x, is_same x x = true.
  Proof.
    intro x; unfold is_same; destruct x as [x0 x1];
      rewrite (A_same.is_same_refl x0); rewrite (B_same.is_same_refl x1); trivial.
  Qed.


  Lemma is_same_sym : forall x y, is_same x y = is_same y x.
    intros x y; destruct x as [x0 x1]; destruct y as [y0 y1]; unfold is_same;
      rewrite (A_same.is_same_sym x0 y0);
      rewrite (B_same.is_same_sym x1 y1);
      reflexivity.
  Qed.
End Same_prod.


Module Type Eqb_arg (M : T).
  Variable eq_dec : forall x y : M.t, {x = y}+{x <> y}.
End Eqb_arg.

(** Represents types that have decidable equality. *)
Module Eqb (M : T) (N : Eqb_arg M).
  Include N.

  (* returns true iff the given keys are equal. *)
  Definition eqb (x y : M.t) : bool :=
    match eq_dec x y with
    | left _  => true
    | right _ => false
    end.

  (** asserts that the equality predicate is reflexive. *)
  Lemma eqb_refl : forall x, eqb x x = true.
  Proof.
    intro x; unfold eqb; destruct (eq_dec x x) as [H|H]; [reflexivity|contradict H; reflexivity].
  Qed.

  (** proves that the key equality predicate only returns true when the given keys are equal. *)
  Lemma eqb_correct : forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y; split; intro H.
    + unfold eqb in H; destruct (eq_dec x y) as [Hxy|Hxy] in H; [exact Hxy|contradict H; discriminate].
    + rewrite H; rewrite (eqb_refl y); reflexivity.
  Qed.

  (** proves that the key equality predicate is symmetric. *)
  Lemma eqb_sym : forall x y, eqb x y = eqb y x.
  Proof.
    intros x y; unfold eqb; destruct eq_dec as [Hxy|Hxy]; destruct eq_dec as [Hyx|Hyx]; try reflexivity.
    + contradiction Hyx; apply eq_sym; assumption.
    + contradiction Hxy; apply eq_sym; assumption.
  Qed.
End Eqb.

Module Type Unique_arg (M : T).
  Include Same (M).
End Unique_arg.

(**
  Defines the is_unique predicate and proves a number of properties that it
  satisfies.
*)
Module Unique (M : T) (N : Unique_arg M).
  Include N.

  (**
    Asserts that the given element is unique within the list - i.e. that only one
    value within the list matches the given element.
  *)
  Fixpoint is_unique (xs : list M.t) (y : M.t) : bool :=
    match xs with
    | nil => true
    | x :: xs =>
      match is_same y x with
      | true => negb (existsb (is_same y) xs)
      | false => is_unique xs y
      end
    end.

  (** Proves that every element in the empty list is unique. *)
  Lemma is_unique_nil : forall y, is_unique nil y = true.
  Proof. intro y; reflexivity. Qed.

  (**
    Proves that if none of the elements in a list match a given element, that
    element is unique in the list.
  *)
  Lemma is_unique_ex (xs : list M.t) (y : M.t)
    : negb (existsb (is_same y) xs) = true -> is_unique xs y = true.
  Proof.
    induction xs as [|x xs F]; [reflexivity|].
    unfold existsb; fold (existsb (is_same y) xs); intro H.
    unfold is_unique.
    destruct (is_same y x); simpl in H.
    + contradict H; discriminate.
    + fold (is_unique xs y); apply (F H).
  Qed.

  (** Proves that if an element is unique in a list it is unique in the tail of the list. *)
  Lemma is_unique_tl (xs : list M.t) (x y : M.t) (Hy_xs : is_unique (x :: xs) y = true)
    : is_unique xs y = true.
  Proof.
    unfold is_unique in Hy_xs.
    destruct (is_same y x) eqn:Hxy.
    + apply (is_unique_ex xs y Hy_xs).
    + fold (is_unique xs y) in Hy_xs; assumption.
  Qed.

  (**
    Proves that none of the remaining elements in a list are the same as a unique
    element at the head of a list.
  *)
  Lemma is_unique_hd (xs : list M.t) (x : M.t) (H : is_unique (x :: xs) x = true)
    : negb (existsb (is_same x) xs) = true.
  Proof.
    unfold is_unique in H; rewrite (is_same_refl x) in H; exact H.
  Qed.

  Lemma is_unique_cons (x : M.t) (xs : list M.t) (x0 : M.t) (Hx_x0 : is_same x x0 = false) (Hx_xs : is_unique xs x = true)
    : is_unique (x0 :: xs) x = true. 
  Proof.
    unfold is_unique; fold (is_unique xs x); destruct (is_same x x0).
    + contradict Hx_x0; discriminate.
    + exact (Hx_xs).
  Qed.

End Unique.

Module Filter_unique (M : T) (N : Unique_arg M).
  Import List_aux.
  Include M.
  Include Unique M N.

  (* asserts that equality is decidable for list elements. *)
  Axiom eq_dec : forall x y : t, x = y \/ x <> y.

  (**
    Accepts a list of elements and removes all of those elements for which one or
    more other elements are the same.

    Note: this function uses a naive algorithm: it iterates over the list of
    elements, checks to see if the element is unique, and adds them to the result
    list iff they are.
  *)

  (* I. the function *)
  Fixpoint remove_not_unique (xs : list t)
    : {ys : list t | forall x, In x xs -> (is_unique xs x = true <-> In x ys)}.
  Proof.
    refine (
      let res_u xs ys := forall x, In x xs -> (is_unique xs x = true <-> In x ys) in
      let res_t xs := {ys : list t | res_u xs ys} in
      match xs with
      | nil => exist (res_u nil) nil (fun _ => False_ind _)
      | x :: xs =>
        let (ys, Hf) := remove_not_unique xs in
        match is_unique (x :: xs) x as b return is_unique (x :: xs) x = b -> _ with
        | true  => fun Hx_xxs => exist _ (x :: ys) _ (* SEE: uniq and inserted *)
        | false => fun Hx_xxs =>
          let zs  := filter (fun y => negb (is_same x y)) ys in
          let Hzs z : In z zs <-> In z ys /\ negb (is_same x z) = true :=
            filter_In (fun y => negb (is_same x y)) z ys
          in
          exist _ zs _ (* SEE: not uniq and filtered *)
        end
        (eq_refl _)
       end
    ).

  (* II. footnote proofs *)

  (* uniq and inserted *)
  + intros y Hy_xxs.
    split; [intro Hy_xxs_uniq|intro Hy_xys].
    - induction Hy_xxs as [Hxy|Hy_xs].
      (* uniq and inserted, uniq => in, x = y *)
      * left; exact Hxy.
      (* uniq and inserted, uniq => in, y in xs *)
      * right; exact (proj1 (Hf y Hy_xs) (is_unique_tl xs x y Hy_xxs_uniq)).
    (* uniq and inserted, in => uniq *)
    - destruct (eq_dec y x) as [Hyx|Hyx].
      (* uniq and inserted, in => uniq, x = y *)
      * rewrite Hyx; assumption.
      (* uniq and inserted, in => uniq, x <> y *)
      * set (Hy_xs := in_tl (not_eq_sym Hyx) Hy_xxs).
        set (Hy_ys := in_tl (not_eq_sym Hyx) Hy_xys).
        set (Hy_xs_uniq := proj2 (Hf y Hy_xs) Hy_ys).
        set (Hx_xs := is_unique_hd xs x Hx_xxs).
        unfold is_unique; fold (is_unique xs y); destruct (is_same y x) eqn:Hyx_same.
        (* uniq and inserted, in => uniq, x <> y, x same y *)
        ** assert (Hx_xs_nuniq : existsb (is_same x) xs = true).
          *** apply (existsb_exists (is_same x) xs).
             exists y; split; [exact Hy_xs|rewrite (is_same_sym x y); exact Hyx_same].
          *** rewrite Hx_xs_nuniq in Hx_xs; contradict Hx_xs; discriminate.
        (* uniq and inserted, in => uniq, x <> y, x not same y *)
        ** exact Hy_xs_uniq.

  (* not uniq and filtered *)
  + intros y Hy_xxs.
    split; [intro Hy_xxs_uniq|intro Hy_zs].
    (* not uniq and filtered, uniq => in *)
    - assert (Hyx_tmp : eq_dec y x = eq_dec y x) by reflexivity;
      induction (eq_dec y x) as [Hyx|Hyx] in Hyx_tmp at 2; clear Hyx_tmp.
      (* not uniq and filtered, uniq => in, y = x *)
      * contradict Hy_xxs_uniq; rewrite Hyx; rewrite Hx_xxs; discriminate.
      (* not uniq and filtered, uniq => in, y <> x *)
      * assert (Hy_xs : In y xs) by apply (in_tl (not_eq_sym Hyx) Hy_xxs).
        assert (Hxy_same : is_same x y = is_same x y) by reflexivity; destruct (is_same x y) in Hxy_same at 2.
        (* not uniq and filtered, uniq => in, y <> x, x same y *)
        ** contradict Hy_xxs_uniq; unfold is_unique; rewrite (is_same_sym y x); rewrite Hxy_same;
          assert (Hy_xs_same : existsb (is_same y) xs = true).
          *** apply (existsb_exists (is_same y) xs); exists y; split; [exact Hy_xs|exact (is_same_refl y)].
          *** rewrite Hy_xs_same; discriminate.
        (* not uniq and filtered, uniq => in, y <> x, x not same y *)
        ** apply (Hzs y); split.
           *** exact (proj1 (Hf y Hy_xs) (is_unique_tl xs x y Hy_xxs_uniq)).
           *** rewrite Hxy_same; reflexivity.
    (* not uniq and filtered, in => uniq *)
    - unfold is_unique.
      fold (is_unique xs y).
      set (Hy_x := proj1 (Hzs y) Hy_zs).
      set (Hy_ys := proj1 Hy_x).
      set (Hy_x_nsame := proj2 Hy_x).
      assert (Hxy_same : is_same x y = is_same x y) by reflexivity; destruct (is_same x y) in Hxy_same at 2.
      (* not uniq and filtered, in => uniq, x same y *)
      * rewrite Hxy_same in Hy_x_nsame; contradict Hy_x_nsame; discriminate.
      (* not uniq and filtered, in => uniq, x not same y *)
      * rewrite (is_same_sym y x); rewrite Hxy_same; destruct Hy_xxs as [Hyx|Hy_xs].
        (* not uniq and filtered, in => uniq, x not same y, x = y *)
        ** contradict Hxy_same; rewrite Hyx; rewrite (is_same_refl y); discriminate.
        (* not uniq and filtered, in => uniq, x not same y, y in xs *)
        ** apply (proj2 (Hf y Hy_xs) Hy_ys).
  Qed.
End Filter_unique.

Module Type Join_arg (A B : T).
  Variable same_key : A.t -> B.t -> bool.
End Join_arg.

Module Join (A B : T) (N : Join_arg A B).

  Fixpoint join_aux (x : A.t) (ys : list B.t) : list (A.t * B.t) :=
    match ys with
    | [] => []
    | y :: ys =>
      let zs := join_aux x ys in
      if N.same_key x y
      then (x, y) :: zs
      else zs
    end.

  (**
    Accepts two datasets, [xs] and [ys], and performs an inner join using the
    same_key predicate - i.e. it returns every pair of values, [x,y] where x is in
    xs and y is in ys, and x and y have the same key.
  *)
  Fixpoint join xs ys : list (A.t * B.t) :=
    match xs with
    | [] => []
    | x :: xs => join_aux x ys ++ join xs ys
    end.

  Lemma join_nil : forall xs, join xs [] = [].
  Proof.
    induction xs as [|x xs Hxs]; [trivial|].
    unfold join; fold (join xs []); rewrite Hxs; simpl; reflexivity.
  Qed.

  Lemma join_aux_cons
    : forall (x : A.t) (y : B.t) (ys : list B.t) (a : A.t) (b : B.t), In (a, b) (join_aux x ys) -> In (a, b) (join_aux x (y :: ys)).
  Proof.
    intros x y; induction ys as [|y1 ys Hys]; intros a b; [contradiction|].
    intro Hab; unfold join_aux; destruct (N.same_key x y) eqn:Hxy; fold (join_aux x (y1 :: ys)).
    + right; exact Hab.
    + exact Hab.
    Qed.

  Lemma join_aux_cons_or
    : forall (x : A.t) (y : B.t) (ys : list B.t) (a : A.t) (b : B.t),
      In (a, b) (join_aux x (y :: ys)) <-> (a = x /\ b = y /\ N.same_key a b = true) \/ In (a, b) (join_aux x ys).
  Proof.
    intros x y ys a b.
    unfold join_aux; destruct (N.same_key x y) eqn:Hxy; fold (join_aux x ys); split; intro H.
    + destruct H.
      - inversion H as [(Hx_a, Hy_b)]; left; rewrite <- Hx_a; rewrite <- Hy_b; exact (conj eq_refl (conj eq_refl Hxy)).
      - right; exact H.
    + destruct H.
      - left; rewrite (proj1 H); rewrite (proj1 (proj2 H)); reflexivity.
      - right; exact H.
    + right; exact H.
    + destruct H.
      - contradict Hxy; rewrite <- (proj1 H); rewrite <- (proj1 (proj2 H)); rewrite (proj2 (proj2 H)); discriminate.
      - exact H.
  Qed.

  Lemma join_aux_snd
    : forall (x : A.t) (ys : list B.t) (a : A.t) (b : B.t),
        In (a, b) (join_aux x ys) -> a = x /\ In b ys.
  Proof.
    intro x; induction ys as [|y0 ys Hys]; intros a b Hab.
      + contradict Hab.
      + destruct (proj1 (join_aux_cons_or x y0 ys a b) Hab) as [H|H].
        - split; [exact (proj1 H)|left; symmetry; exact (proj1 (proj2 H))].
        - set (Hx_ys := Hys a b H).
          split; [exact (proj1 Hx_ys)|right; exact (proj2 Hx_ys)].
  Qed.

  Lemma join_aux_in
    : forall (x : A.t) (ys : list B.t) (a : A.t) (b : B.t), In (a, b) (join_aux x ys) <-> (a = x /\ In b ys /\ N.same_key a b = true).
  Proof.
    intro x; induction ys as [|y ys Hys]; intros a b; split; try contradiction.
    + intro Hcontr; contradict (proj1 (proj2 Hcontr)). 

    + intro Hab; set (H := proj1 (join_aux_cons_or x y ys a b) Hab).
      destruct H.
      - exact (conj (proj1 H) (conj (or_introl (eq_sym (proj1 (proj2 H)))) (proj2 (proj2 H)))).
      - set (Hab_ys := proj1 (Hys a b) H).
        exact (conj (proj1 Hab_ys) (conj (or_intror (proj1 (proj2 Hab_ys))) (proj2 (proj2 Hab_ys)))).
    + intro Hab_yys; apply (proj2 (join_aux_cons_or x y ys a b)).
      destruct (proj1 (proj2 Hab_yys)) as [Hyb|Hb_ys].
      - left; exact (conj (proj1 Hab_yys) (conj (eq_sym Hyb) (proj2 (proj2 Hab_yys)))).
      - right; apply (proj2 (Hys a b)).
        exact (conj (proj1 Hab_yys) (conj Hb_ys (proj2 (proj2 Hab_yys)))).
  Qed.
      
  Theorem join_in 
    : forall (xs : list A.t) (ys : list B.t) (x : A.t) (y : B.t), (In (x, y) (join xs ys) <-> (In x xs /\ In y ys /\ N.same_key x y = true)).
  Proof.
    intro xs; induction xs as [|x xs F ys].
    (* xs = [] *)
    + intros ys x y; split; [contradiction|intro Hcontr; contradict (proj1 Hcontr)].
    + intro ys; induction ys as [|y ys G].
      (* ys = [] *)
      - intros a b; split.
        * rewrite (join_nil (x :: xs)); contradiction.
        * intro Hcontr; contradict (proj1 (proj2 Hcontr)).
      - intros a b; split; unfold join; fold (join xs (y :: ys)).
        * intro Hab_app.
          destruct (in_app_or (join_aux x (y :: ys)) (join xs (y :: ys)) (a, b) Hab_app) as [Hab|Hab].
          ** set (H := proj1 (join_aux_in x (y :: ys) a b) Hab).
             exact (conj (or_introl (eq_sym (proj1 H))) (proj2 H)).
          ** set (H := proj1 (F (y :: ys) a b) Hab). 
             exact (conj (or_intror (proj1 H)) (proj2 H)).
        * intro Hab; destruct (proj1 Hab) as [Hx_a|Ha_xs].
          ** apply (in_or_app (join_aux x (y :: ys)) (join xs (y :: ys))); left.
             apply (proj2 (join_aux_in x (y :: ys) a b)).
             exact (conj (eq_sym Hx_a) (proj2 Hab)).
          ** apply (in_or_app (join_aux x (y :: ys)) (join xs (y :: ys))); right.
             apply (proj2 (F (y :: ys) a b)).
             exact (conj Ha_xs (proj2 Hab)).
  Qed.

  Module Type Join_unique_arg.
    Declare Module A_same : Same A.
    Declare Module B_same : Same B.
  End Join_unique_arg.

  Module Join_unique (M : Join_unique_arg).
    Module A_unique := Unique A M.A_same.
    Module B_unique := Unique B M.B_same.
    Module AB := Prod_t A B.
    Module AB_same := Same_prod A B M.A_same M.B_same.
    Module AB_unique := Unique AB AB_same.

    Import List_aux.
    Open Scope bool_scope.

    Lemma join_aux_none
      :  forall (x : A.t) (b : B.t) (ys : list B.t),
           (forall y, In y ys -> M.B_same.is_same y b = false) ->
           negb (existsb (fun z => AB_unique.is_same z (x, b)) (join_aux x ys)) = true.
    Proof.
      intros x b ys Hy_ys.
      apply (proj2 (negb_existsb _ _)).
      intros z Hz_zs.
      destruct z as [z0 y].
      set (Hxy := join_aux_snd x ys z0 y Hz_zs).
      rewrite (proj1 Hxy).
      simpl; rewrite (M.A_same.is_same_refl x).
      simpl; exact (Hy_ys y (proj2 Hxy)).
    Qed.

    Lemma join_aux_not_same_x
      :  forall (a : A.t) (b : B.t) (bs : list B.t),
           N.same_key a b = false -> 
           negb (existsb (AB_unique.is_same (a, b)) (join_aux a bs)) = true.
    Proof.
      intros a b; induction bs as [|b0 bs Hbs]; intro Hab.
      + reflexivity.
      + simpl.
        apply (proj2 (negb_existsb _ _)).
        intros (x, y) Hxy.
        unfold AB_unique.is_same.


    Lemma join_aux_uniq
      :  forall (x : A.t) (ys : list B.t) (y : B.t),
           B_unique.is_unique ys y = true -> In (x, y) (join_aux x ys) ->
           AB_unique.is_unique (join_aux x ys) (x, y) = true.
    Proof.
     intros x ys y Hy_uniq Hxy_zs.
     destruct ys as [|y0 ys]; [reflexivity|].
     unfold join_aux; destruct (N.same_key x y0); fold (join_aux x ys).
     + unfold AB_unique.is_unique; destruct (AB_unique.is_same (x, y) (x, y0)) eqn:Hxy_xy0; fold (AB_unique.is_unique (join_aux x ys) (x, y)).
       - apply (proj2 (negb_existsb _ _)).
         intros (a, b) Hab.
         simpl.
         simpl in Hxy_xy0.
      

       - rewrite <- existsb_forallb.
         apply (proj2 (forallb_forall _ _)).
         intros (a, b) Hz_zs.
         destruct (AB_unique.is_same (x, y) (a, b)) eqn:Hxy_ab.
         * unfold B_unique.is_unique in Hy_uniq.
           simpl in Hxy_xy0.
           set (Hyy0 := proj2 (andb_prop _ _ Hxy_xy0)).
           rewrite Hyy0 in Hy_uniq.
           rewrite <- (existsb_forallb _ _) in Hy_uniq.
           set (Hy_ys := proj1 (forallb_forall _ _) Hy_uniq).

SearchPattern (_ && _ = true -> _).




      intro x. induction ys as [|y0 ys Hys]; intros y Hy_ys Hxy_zs; [reflexivity|].
      set (Hxy_yys := proj1 (join_aux_cons_or x y0 ys x y) Hxy_zs).
      unfold join_aux; destruct (N.same_key x y0); fold (join_aux x ys);
        destruct Hxy_yys.
      + simpl.
        rewrite (proj1 (proj2 H)).
        rewrite (M.A_same.is_same_refl x).
        rewrite (M.B_same.is_same_refl y0).
        simpl.
        simpl in Hy_ys.
        rewrite (proj1 (proj2 H)) in Hy_ys.
        rewrite (M.B_same.is_same_refl y0) in Hy_ys.
        rewrite <- (existsb_forallb (B_unique.is_same y0) ys) in Hy_ys.
        set (Hys_uniq := proj1 (forallb_forall _ ys) Hy_ys).
        rewrite <- (existsb_forallb (AB_unique.is_same (x, y0)) (join_aux x ys)).
        apply (proj2 (forallb_forall (fun z => negb (AB_unique.is_same (x, y0) z)) (join_aux x ys))).
        intros z Hz_zs.
        destruct (AB_unique.is_same (x, y0) z) eqn:Hz.
        - unfold AB_unique.is_same in Hz.
        

 Search "forallb".

        destruct (existsb (B_unique.is_same y0) ys) eqn:Hy0_ys.
        - contradict Hy_ys; discriminate.
        - Search "existsb".


        destruct (existsb (AB_unique.is_same (x, y0)) (join_aux x ys)) eqn:Hxy0.
        - set (Hcontr := proj1 (existsb_exists (AB_unique.is_same (x, y0)) (join_aux x ys)) Hxy0).
          

Search "existsb".
SearchPattern (forallb _ = (existsb _ _)).
(* TODO
    Lemma join_uniq
      :  forall (xs : list A.t) (ys : list B.t) (x : A.t) (y : B.t),
           In x xs -> In y ys -> A_unique.is_unique xs x = true -> B_unique.is_unique ys y = true ->
           AB_unique.is_unique (proj1_sig (join xs ys)) (x, y) = true.
    Proof.
      intros xs ys x y Hx_xs Hy_ys H_x_xs_uniq H_y_ys_uniq.
*)

  End Join_unique.
End Join.

Module Type Alist_arg (A K : T).
  Include Same A.
  Include Eqb_arg K.

  Variable val_key : A.t -> K.t.
End Alist_arg.

Module Alist (A K : T) (M : Alist_arg A K).
  Import List_aux.
  Include Eqb K M.

  (* asserts that equality is decidable for list elements. *)
  Axiom a_eq_dec : forall x y : A.t, x = y \/ x <> y.

  (** represents entries in an associative list. *)
  Definition entry : Set := K.t * list A.t.

  Definition key (xs : entry) := fst xs.

  Definition vals (xs : entry) := snd xs.

  Definition same_key (xs ys : entry) : bool := eqb (key xs) (key ys).

  (** represents associative lists. *)
  Definition alist : Set := list (K.t * list A.t).

  (**
    returns either a proof that the associative list contains an entry under the
    given key or a proof that none of the entries have the given key.
  *)
  Definition k_exists (xss : alist) (k : K.t)
    :  {exists xs, key xs = k /\ In xs xss}+{Forall (fun xs => key xs <> k) xss}
    := list_rec
         (fun xss => {exists xs, key xs = k /\ In xs xss}+{Forall (fun xs => key xs <> k) xss})
         (right (Forall_nil _))
         (fun xs xss' F => 
           match eq_dec (key xs) k with
           | left  H => left (ex_intro _ xs (conj H (or_introl (eq_refl _))))
           | right H =>
             match F with
             | left  H_rec => left (
               match H_rec with
               | ex_intro _ ys Hys => ex_intro _ ys (conj (proj1 Hys) (or_intror _ (proj2 Hys)))
               end)
             | right H_rec => right (Forall_cons xs H H_rec)
             end
           end)
         xss.

  Definition k_existsb (xss : alist) (k : K.t) : bool :=
    match k_exists xss k with
    | left  _ => true
    | right _ => false
    end.

  (** proves that existsb returns true iff the given key exists. *)
  Lemma k_existsb_correct : forall xss k, k_existsb xss k = true <-> exists xs, key xs = k /\ In xs xss.
  Proof.
    intros xss k; split; unfold k_existsb; destruct (k_exists xss k) as [H|H]; intro H0; try assumption; try reflexivity.
    + contradict H0; discriminate.
    + exfalso; destruct H0 as [(j, xs)]; exact (proj1 (Forall_forall _ xss) H (j, xs) (proj2 H0) (proj1 H0)).
  Qed.

  (** inserts the given value into the correct entry in the associative list. *)
  Definition insert (xss : alist) (k : K.t) (Hk : exists xs, key xs = k /\ In xs xss) (x : A.t)
    : {yss : alist |
        Forall2 (fun ys xs =>
          (key xs = key ys) /\
          (key xs = k -> vals ys = x :: vals xs) /\
          (key xs <> k -> ys = xs))
          yss xss}.

  (* I. the function *)
  Proof. refine (
    list_rec
      (fun xss' =>
        {yss : alist |
          Forall2 (fun ys xs =>
            (key xs = key ys) /\
            (key xs = k -> vals ys = x :: vals xs) /\
            (key xs <> k -> ys = xs))
            yss xss'})
      (exist _ nil (Forall2_nil _))
      (fun xs xss' F =>
        let (yss, Hyss) := F in
        match eq_dec (key xs) k with 
        | left Hk  =>
          let zs := (key xs, x :: vals xs) in
          exist _ (zs :: yss) _ (* See add *)
        | right Hk =>
          exist _ (xs :: yss) _ (* See skip *)
        end)
      xss).

    (* II. Footnote proofs. *)
    (* add *)
    + apply (Forall2_cons zs xs); [|exact Hyss]; split; [reflexivity|]; split; intro H; [reflexivity|contradiction H].
    (* skip *)
    + apply (Forall2_cons xs xs); [|exact Hyss]; split; [reflexivity|]; split; intro H; [contradiction Hk|reflexivity].
  Qed.

  (**
    groups the given values into an associative
    Note: this spec is under specified. As written, we could have an associative
    list in which each element is in its own entry. More generally, this spec does
    not preclude multiple entries for the same key.
  *)
  Fixpoint group (xs : list A.t)
    : {yss : alist | forall x, In x xs <-> exists ys, In ys yss /\ key ys = M.val_key x /\ In x (vals ys)}.
   Proof. refine (
     match xs with
     | nil => exist _ nil _ (* See: nil *)
     | x :: xs' =>
       let k := M.val_key x in
       let (yss, Hyss) := group xs' in
       match k_exists yss k with
       | left Hk =>
         let (zss, Hzss) := insert yss k Hk x in
         exist _ zss _ (* See: inserted *)
       | right Hk =>
         let zs := (k, [x]) in
         exist _ (zs :: yss) _ (* See: added *)
       end
     end
   ).

  (* nil *)
  +  intro a; split; intro Hcontr; [contradiction|].
     - destruct Hcontr as [(ys, Hys)]; contradiction (proj1 H).
  (* inserted *)
  + intro a; split.
    - intro Ha_xxs. 
      destruct (a_eq_dec x a) as [Hxa|Hxa] in Ha_xxs.
      * assert (Hzs : exists zs, In zs zss /\ key zs = k /\ In x (vals zs)).
        ** destruct Hk as [ys Hys].
           destruct (Forall2_forall_r _ zss yss Hzss ys (proj2 Hys)) as [zs Hzs].
           assert (Hzs_k : key zs = k) by (rewrite <- (proj1 Hys); symmetry; exact (proj1 (proj2 Hzs))).
           exists zs; split; [exact (proj1 Hzs)|]; split; [exact Hzs_k|].
           *** rewrite (proj1 (proj2 (proj2 Hzs)) (proj1 Hys)); left; reflexivity.
        ** destruct Hzs as [zs Hzs].
           exists zs; split; [exact (proj1 Hzs)|]; rewrite <- Hxa; exact (proj2 Hzs).
      * assert (Ha_xs : In a xs') by exact (in_tl Hxa Ha_xxs).
        destruct (proj1 (Hyss a) Ha_xs) as [ys Hys].
        destruct (Forall2_forall_r _ zss yss Hzss ys (proj1 Hys)) as [zs Hzs].
        exists zs; split; [exact (proj1 Hzs)|]; split;
          [rewrite <- (proj1 (proj2 Hzs)); rewrite (proj1 (proj2 Hys)); reflexivity|].
        destruct (eq_dec k (key ys)) as [Hkj|Hkj].
        ** rewrite (proj1 (proj2 (proj2 Hzs)) (eq_sym Hkj)); right; exact (proj2 (proj2 Hys)).
        ** rewrite (proj2 (proj2 (proj2 Hzs)) (not_eq_sym Hkj)); exact (proj2 (proj2 Hys)).
    - intro Hzs_ex.
      destruct Hzs_ex as [zs Hzs].
      destruct (Forall2_forall _ zss yss Hzss zs (proj1 Hzs)) as [ys Hys].
      destruct (eq_dec (key ys) k) as [Hjk|Hjk].
      * destruct (a_eq_dec x a) as [Hxa|Hxa].
        ** rewrite Hxa; left; reflexivity.
        ** right; apply (proj2 (Hyss a)).
           exists ys; split; [exact (proj1 Hys)|]; split. 
           *** rewrite (proj1 (proj2 Hys)); rewrite (proj1 (proj2 Hzs)); reflexivity.
           *** rewrite (proj1 (proj2 (proj2 Hys)) Hjk) in Hzs.
               exact (in_tl Hxa (proj2 (proj2 Hzs))).
      * right; apply (proj2 (Hyss a)).
        exists ys; split; [exact (proj1 Hys)|]; split.
        ** rewrite <- (proj1 (proj2 Hzs)); rewrite (proj1 (proj2 Hys)); reflexivity.
        ** rewrite <- (proj2 (proj2 (proj2 Hys)) Hjk); exact (proj2 (proj2 Hzs)).
  (* added *)
  + intro a; split.
    - intro Ha_xxs; destruct Ha_xxs as [Hax|Ha_xs].
      * exists zs; split; [left; reflexivity|]; rewrite <- Hax; split; [reflexivity|left; reflexivity].
      * destruct (proj1 (Hyss a) Ha_xs) as [ys Hys]; exists ys; split; [right; exact (proj1 Hys)|exact (proj2 Hys)].
    - intro Hys_ex; destruct Hys_ex as [ys Hys].
      destruct (proj1 Hys) as [Hzs_ys|Hys_yss].
      * rewrite <- Hzs_ys in Hys; destruct (proj2 (proj2 Hys)) as [Hxa|Ha_nil].
        ** rewrite Hxa; left; reflexivity.
        ** contradiction Ha_nil.
      * right; exact (proj2 (Hyss a) (ex_intro _ ys (conj Hys_yss (proj2 Hys)))).
  Qed.
End Alist.

Module Int.
  Definition t := nat.

  Definition eq_dec := PeanoNat.Nat.eq_dec.
End Int.

Module Str.
  Definition t := string.


  Definition eq_dec := string_dec.
End Str.
