From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import intro_patterns spec_patterns sel_patterns.
From iris.bi Require Export bi.
From iris.proofmode Require Export classes notation.
From iris.proofmode Require Import class_instances.
From stdpp Require Import stringmap hlist.
From iris.proofmode Require Import strings.
Set Default Proof Using "Type".

Declare Reduction env_cbv := cbv [
  beq ascii_beq string_beq
  env_lookup env_lookup_delete env_delete env_app env_replace env_dom
  env_persistent env_spatial env_spatial_is_nil envs_dom
  envs_lookup envs_lookup_delete envs_delete envs_snoc envs_app
    envs_simple_replace envs_replace envs_split
    envs_clear_spatial envs_clear_persistent
    envs_split_go envs_split].
Ltac env_cbv :=
  match goal with |- ?u => let v := eval env_cbv in u in change v end.
Ltac env_reflexivity := env_cbv; reflexivity.

(** * Misc *)
(* Tactic Notation tactics cannot return terms *)
Ltac iFresh' H :=
  lazymatch goal with
  |- of_envs ?Δ ⊢ _ =>
     (* [vm_compute fails] if any of the hypotheses in [Δ] contain evars, so
     first use [cbv] to compute the domain of [Δ] *)
     let Hs := eval cbv in (envs_dom Δ) in
     eval vm_compute in (fresh_string_of_set H (of_list Hs))
  | _ => H
  end.
Ltac iFresh := iFresh' "~".

Ltac iMissingHyps Hs :=
  let Δ :=
    lazymatch goal with
    | |- of_envs ?Δ ⊢ _ => Δ
    | |- context[ envs_split _ _ ?Δ ] => Δ
    end in
  let Hhyps := eval env_cbv in (envs_dom Δ) in
  eval vm_compute in (list_difference Hs Hhyps).

Ltac iTypeOf H :=
  let Δ := match goal with |- of_envs ?Δ ⊢ _ => Δ end in
  eval env_cbv in (envs_lookup H Δ).

Tactic Notation "iMatchHyp" tactic1(tac) :=
  match goal with
  | |- context[ environments.Esnoc _ ?x ?P ] => tac x P
  end.

Class AsValid {PROP : bi} (φ : Prop) (P : PROP) := as_entails : φ ↔ P.
Arguments AsValid {_} _%type _%I.

Instance as_valid_valid {PROP : bi} (P : PROP) : AsValid (bi_valid P) P | 0.
Proof. by rewrite /AsValid. Qed.

Instance as_valid_entails {PROP : bi} (P Q : PROP) : AsValid (P ⊢ Q) (P -∗ Q) | 1.
Proof. split. apply bi.entails_wand. apply bi.wand_entails. Qed.

Instance as_valid_equiv {PROP : bi} (P Q : PROP) : AsValid (P ≡ Q) (P ∗-∗ Q).
Proof. split. apply bi.equiv_wand_iff. apply bi.wand_iff_equiv. Qed.

(** * Start a proof *)
Ltac iStartProof :=
  lazymatch goal with
  | |- of_envs _ ⊢ _ => idtac
  | |- ?P =>
    apply (proj2 (_ : AsValid P _)), tac_adequate
    || fail "iStartProof: not a BI entailment"
  end.

(** * Context manipulation *)
Tactic Notation "iRename" constr(H1) "into" constr(H2) :=
  eapply tac_rename with _ H1 H2 _ _; (* (i:=H1) (j:=H2) *)
    [env_reflexivity || fail "iRename:" H1 "not found"
    |env_reflexivity || fail "iRename:" H2 "not fresh"|].

Local Inductive esel_pat :=
  | ESelPure
  | ESelName : bool → string → esel_pat.

Ltac iElaborateSelPat pat :=
  let rec go pat Δ Hs :=
    lazymatch pat with
    | [] => eval cbv in Hs
    | SelPure :: ?pat => go pat Δ (ESelPure :: Hs)
    | SelPersistent :: ?pat =>
       let Hs' := eval env_cbv in (env_dom (env_persistent Δ)) in
       let Δ' := eval env_cbv in (envs_clear_persistent Δ) in
       go pat Δ' ((ESelName true <$> Hs') ++ Hs)
    | SelSpatial :: ?pat =>
       let Hs' := eval env_cbv in (env_dom (env_spatial Δ)) in
       let Δ' := eval env_cbv in (envs_clear_spatial Δ) in
       go pat Δ' ((ESelName false <$> Hs') ++ Hs)
    | SelName ?H :: ?pat =>
       lazymatch eval env_cbv in (envs_lookup_delete H Δ) with
       | Some (?p,_,?Δ') => go pat Δ' (ESelName p H :: Hs)
       | None => fail "iElaborateSelPat:" H "not found"
       end
    end in
  lazymatch goal with
  | |- of_envs ?Δ ⊢ _ =>
    let pat := sel_pat.parse pat in go pat Δ (@nil esel_pat)
  end.

Tactic Notation "iClear" constr(Hs) :=
  let rec go Hs :=
    lazymatch Hs with
    | [] => idtac
    | ESelPure :: ?Hs => clear; go Hs
    | ESelName _ ?H :: ?Hs =>
       eapply tac_clear with _ H _ _; (* (i:=H) *)
         [env_reflexivity || fail "iClear:" H "not found"
         |env_cbv; exact tt || apply _ || fail "iClear: " H "not affine" (* TODO *)
         |go Hs]
    end in
  let Hs := iElaborateSelPat Hs in go Hs.

Tactic Notation "iClear" "(" ident_list(xs) ")" constr(Hs) :=
  iClear Hs; clear xs.

(** * Assumptions *)
Tactic Notation "iExact" constr(H) :=
  eapply tac_assumption with _ H _ _; (* (i:=H) *)
    [env_reflexivity || fail "iExact:" H "not found"
    |apply _ ||
     let P := match goal with |- FromAssumption _ ?P _ => P end in
     fail "iExact:" H ":" P "does not match goal"
    |env_cbv; apply _ || fail "iExact: TODO"].

Tactic Notation "iAssumptionCore" :=
  let rec find Γ i P :=
    match Γ with
    | Esnoc ?Γ ?j ?Q => first [unify P Q; unify i j|find Γ i P]
    end in
  match goal with
  | |- envs_lookup ?i (Envs ?Γp ?Γs) = Some (_, ?P) =>
     first [is_evar i; fail 1 | env_reflexivity]
  | |- envs_lookup ?i (Envs ?Γp ?Γs) = Some (_, ?P) =>
     is_evar i; first [find Γp i P | find Γs i P]; env_reflexivity
  | |- envs_lookup_delete ?i (Envs ?Γp ?Γs) = Some (_, ?P, _) =>
     first [is_evar i; fail 1 | env_reflexivity]
  | |- envs_lookup_delete ?i (Envs ?Γp ?Γs) = Some (_, ?P, _) =>
     is_evar i; first [find Γp i P | find Γs i P]; env_reflexivity
  end.

Tactic Notation "iAssumption" :=
  let Hass := fresh in
  let rec find p Γ Q :=
    match Γ with
    | Esnoc ?Γ ?j ?P => first
       [pose proof (_ : FromAssumption p P Q) as Hass;
        eapply (tac_assumption _ _ j p P);
          [env_reflexivity
          |apply Hass
          |env_cbv; apply _ || fail "iAssumption: TODO"]
       |assert (P = False%I) as Hass by reflexivity;
        apply (tac_false_destruct _ j p P);
          [env_reflexivity
          |exact Hass]
       |find p Γ Q]
    end in
  match goal with
  | |- of_envs (Envs ?Γp ?Γs) ⊢ ?Q =>
     first [find true Γp Q | find false Γs Q
           |fail "iAssumption:" Q "not found"]
  end.

(** * False *)
Tactic Notation "iExFalso" := apply tac_ex_falso.

(** * Making hypotheses persistent or pure *)
Local Tactic Notation "iPersistent" constr(H) :=
  eapply tac_persistent with _ H _ _ _; (* (i:=H) *)
    [env_reflexivity || fail "iPersistent:" H "not found"
    |apply _ ||
     let Q := match goal with |- IntoPersistentP ?Q _ => Q end in
     fail "iPersistent:" Q "not persistent"
    |env_cbv; apply _ || fail "iPersistent: TODO"
    |env_reflexivity|].

Local Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
  eapply tac_pure with _ H _ _ _; (* (i:=H1) *)
    [env_reflexivity || fail "iPure:" H "not found"
    |apply _ ||
     let P := match goal with |- IntoPure ?P _ => P end in
     fail "iPure:" P "not pure"
    |env_cbv; apply _ || fail "iPure: TODO"
    |intros pat].

Tactic Notation "iEmpIntro" :=
  iStartProof;
  eapply tac_emp_intro;
    [env_reflexivity || fail "iEmpIntro: spatial context is non-empty"].

Tactic Notation "iPureIntro" :=
  iStartProof;
  eapply tac_pure_intro;
    [apply _ ||
     let P := match goal with |- FromPure ?P _ => P end in
     fail "iPureIntro:" P "not pure"
    |].

(** Framing *)
Local Ltac iFrameFinish :=
  lazy iota beta;
  try match goal with
  | |- _ ⊢ True => exact (bi.pure_intro _ _ I)
  | |- _ ⊢ emp => iEmpIntro
  end.

Local Ltac iFramePure t :=
  let φ := type of t in
  eapply (tac_frame_pure _ _ _ _ t);
    [apply _ || fail "iFrame: cannot frame" φ
    |iFrameFinish].

Local Ltac iFrameHyp H :=
  eapply tac_frame with _ H _ _ _;
    [env_reflexivity || fail "iFrame:" H "not found"
    |apply _ ||
     let R := match goal with |- Frame _ ?R _ _ => R end in
     fail "iFrame: cannot frame" R
    |iFrameFinish].

Local Ltac iFrameAnyPure :=
  repeat match goal with H : _ |- _ => iFramePure H end.

Local Ltac iFrameAnyPersistent :=
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- of_envs ?Δ ⊢ _ =>
     let Hs := eval cbv in (env_dom (env_persistent Δ)) in go Hs
  end.

Local Ltac iFrameAnySpatial :=
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- of_envs ?Δ ⊢ _ =>
     let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
  end.

Tactic Notation "iFrame" := iFrameAnySpatial.

Tactic Notation "iFrame" "(" constr(t1) ")" :=
  iFramePure t1.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" :=
  iFramePure t1; iFrame ( t2 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" :=
  iFramePure t1; iFrame ( t2 t3 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ).

Tactic Notation "iFrame" constr(Hs) :=
  let rec go Hs :=
    lazymatch Hs with
    | [] => idtac
    | SelPure :: ?Hs => iFrameAnyPure; go Hs
    | SelPersistent :: ?Hs => iFrameAnyPersistent; go Hs
    | SelSpatial :: ?Hs => iFrameAnySpatial; go Hs
    | SelName ?H :: ?Hs => iFrameHyp H; go Hs
    end
  in let Hs := sel_pat.parse Hs in go Hs.
Tactic Notation "iFrame" "(" constr(t1) ")" constr(Hs) :=
  iFramePure t1; iFrame Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")"
    constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ) Hs.

(** * Basic introduction tactics *)
Local Tactic Notation "iIntro" "(" simple_intropattern(x) ")" :=
  try iStartProof;
  try first
    [(* (∀ _, _) *) apply tac_forall_intro
    |(* (?P → _) *) eapply tac_impl_intro_pure;
      [apply _ ||
       let P := match goal with |- IntoPure ?P _ => P end in
       fail "iIntro:" P "not pure"
      |]
    |(* (?P -∗ _) *) eapply tac_wand_intro_pure;
      [apply _ ||
       let P := match goal with |- IntoPure ?P _ => P end in
       fail "iIntro:" P "not pure"
      |apply _ ||
       fail "iIntro: TODO"
      |]
    |(* ⌜∀ _, _⌝ *) apply tac_pure_forall_intro
    |(* ⌜_ → _⌝ *) apply tac_pure_impl_intro];
  intros x.

Local Tactic Notation "iIntro" constr(H) :=
  iStartProof;
  first
  [ (* (?Q → _) *)
    eapply tac_impl_intro with _ H; (* (i:=H) *)
      [reflexivity || fail 1 "iIntro: introducing" H
                             "into non-empty spatial context"
      |env_reflexivity || fail 1 "iIntro:" H "not fresh"
      |]
  | (* (_ -∗ _) *)
    eapply tac_wand_intro with _ H; (* (i:=H) *)
      [env_reflexivity || fail 1 "iIntro:" H "not fresh"
      |]
  | fail 1 "iIntro: nothing to introduce" ].

Local Tactic Notation "iIntro" "#" constr(H) :=
  iStartProof;
  first
  [ (* (?P → _) *)
    eapply tac_impl_intro_persistent with _ H _; (* (i:=H) *)
      [apply _ || 
       let P := match goal with |- IntoPersistentP ?P _ => P end in
       fail 1 "iIntro: " P " not persistent"
      |env_reflexivity || fail 1 "iIntro:" H "not fresh"
      |]
  | (* (?P -∗ _) *)
    eapply tac_wand_intro_persistent with _ H _; (* (i:=H) *)
      [apply _ || 
       let P := match goal with |- IntoPersistentP ?P _ => P end in
       fail 1 "iIntro: " P " not persistent"
      |apply _ || fail 1 "iIntro: TODO"
      |env_reflexivity || fail 1 "iIntro:" H "not fresh"
      |]
  | fail 1 "iIntro: nothing to introduce" ].

Local Tactic Notation "iIntro" "_" :=
  try iStartProof;
  first
  [ (* (?Q → _) *) apply tac_impl_intro_drop
  | (* (_ -∗ _) *)
    apply tac_wand_intro_drop;
      [apply _ || fail 1 "iIntro: TODO"
      |]
  | (* (∀ _, _) *) iIntro (_)
  | fail 1 "iIntro: nothing to introduce" ].

Local Tactic Notation "iIntroForall" :=
  try iStartProof;
  lazymatch goal with
  | |- ∀ _, ?P => fail
  | |- ∀ _, _ => intro
  | |- _ ⊢ (∀ x : _, _) => let x' := fresh x in iIntro (x')
  end.
Local Tactic Notation "iIntro" :=
  try iStartProof;
  lazymatch goal with
  | |- _ → ?P => intro
  | |- _ ⊢ (_ -∗ _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
  | |- _ ⊢ (_ → _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
  end.

(** * Specialize *)
Record iTrm {X As} :=
  ITrm { itrm : X ; itrm_vars : hlist As ; itrm_hyps : string }.
Arguments ITrm {_ _} _ _ _.

Notation "( H $! x1 .. xn )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) "") (at level 0, x1, xn at level 9).
Notation "( H $! x1 .. xn 'with' pat )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) pat) (at level 0, x1, xn at level 9).
Notation "( H 'with' pat )" := (ITrm H hnil pat) (at level 0).

Local Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
  let rec go xs :=
    lazymatch xs with
    | hnil => idtac
    | hcons ?x ?xs =>
       eapply tac_forall_specialize with _ H _ _ _; (* (i:=H) (a:=x) *)
         [env_reflexivity || fail 1 "iSpecialize:" H "not found"
         |apply _ ||
          let P := match goal with |- IntoForall ?P _ => P end in
          fail 1 "iSpecialize: cannot instantiate" P "with" x
         |exists x; split; [env_reflexivity|go xs]]
    end in
  go xs.

Local Tactic Notation "iSpecializePat" constr(H) constr(pat) :=
  let solve_to_wand H1 :=
    apply _ ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand" in
  let rec go H1 pats :=
    lazymatch pats with
    | [] => idtac
    | SForall :: ?pats =>
       idtac "the * specialization pattern is deprecated because it is applied implicitly";
       go H1 pats
    | SName ?H2 :: ?pats =>
       eapply tac_specialize with _ _ H2 _ H1 _ _ _ _; (* (j:=H1) (i:=H2) *)
         [env_reflexivity || fail "iSpecialize:" H2 "not found"
         |env_reflexivity || fail "iSpecialize:" H1 "not found"
         |apply _ ||
          let P := match goal with |- IntoWand ?P ?Q _ => P end in
          let Q := match goal with |- IntoWand ?P ?Q _ => Q end in
          fail "iSpecialize: cannot instantiate" P "with" Q
         |env_reflexivity|go H1 pats]
    | SPureGoal ?d :: ?pats =>
       eapply tac_specialize_assert_pure with _ H1 _ _ _ _ _;
         [env_reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |apply _ ||
          let Q := match goal with |- FromPure ?Q _ => Q end in
          fail "iSpecialize:" Q "not pure"
         |env_reflexivity
         |done_if d (*goal*)
         |go H1 pats]
    | SGoal (SpecGoal GPersistent false ?Hs_frame [] ?d) :: ?pats =>
       eapply tac_specialize_assert_persistent with _ _ H1 _ _ _ _;
         [env_reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |apply _ ||
          let Q := match goal with |- PersistentP ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |env_reflexivity
         |iFrame Hs_frame; done_if d (*goal*)
         |go H1 pats]
    | SGoal (SpecGoal GPersistent _ _ _ _) :: ?pats =>
       fail "iSpecialize: cannot select hypotheses for persistent premise"
    | SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d) :: ?pats =>
       let Hs' := eval cbv in (if lr then Hs else Hs_frame ++ Hs) in
       eapply tac_specialize_assert with _ _ _ H1 _ lr Hs' _ _ _ _;
         [env_reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |lazymatch m with
          | GSpatial => apply elim_modal_dummy
          | GModal => apply _ || fail "iSpecialize: goal not a modality"
          end
         |env_reflexivity ||
          let Hs' := iMissingHyps Hs' in
          fail "iSpecialize: hypotheses" Hs' "not found"
         |iFrame Hs_frame; done_if d (*goal*)
         |go H1 pats]
    | SAutoFrame GPersistent :: ?pats =>
       eapply tac_specialize_assert_persistent with _ _ H1 _ _ _ _;
         [env_reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |apply _ ||
          let Q := match goal with |- PersistentP ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |env_reflexivity
         |solve [iFrame "∗ #"]
         |go H1 pats]
    | SAutoFrame ?m :: ?pats =>
       eapply tac_specialize_frame with _ H1 _ _ _ _ _ _;
         [env_reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |lazymatch m with
          | GSpatial => apply elim_modal_dummy
          | GModal => apply _ || fail "iSpecialize: goal not a modality"
          end
         |iFrame "∗ #"; apply tac_unlock ||
          fail "iSpecialize: premise cannot be solved by framing"
         |reflexivity]; iIntro H1; go H1 pats
    end in let pats := spec_pat.parse pat in go H pats.

(* The argument [p] denotes whether the conclusion of the specialized term is
persistent. If so, one can use all spatial hypotheses for both proving the
premises and the remaning goal. The argument [p] can either be a Boolean or an
introduction pattern, which will be coerced into [true] when it solely contains
`#` or `%` patterns at the top-level.

In case the specialization pattern in [t] states that the modality of the goal
should be kept for one of the premises (i.e. [>[H1 .. Hn]] is used) then [p]
defaults to [false] (i.e. spatial hypotheses are not preserved). *)
Tactic Notation "iSpecializeCore" open_constr(t) "as" constr(p) :=
  let p := intro_pat_persistent p in
  let t :=
    match type of t with string => constr:(ITrm t hnil "") | _ => t end in
  lazymatch t with
  | ITrm ?H ?xs ?pat =>
    let pat := spec_pat.parse pat in
    lazymatch type of H with
    | string =>
      lazymatch eval compute in (p && negb (existsb spec_pat_modal pat)) with
      | true =>
         eapply tac_specialize_persistent_helper with _ H _ _ _ _;
           [env_reflexivity || fail "iSpecialize:" H "not found"
           |env_cbv; apply _ || fail "iSpecialize: TODO"
           |iSpecializeArgs H xs; iSpecializePat H pat; last (iExact H)
           |apply _ ||
            let Q := match goal with |- PersistentP ?Q => Q end in
            fail "iSpecialize:" Q "not persistent"
           |apply _
           |env_reflexivity|(* goal *)]
      | false => iSpecializeArgs H xs; iSpecializePat H pat
      end
    | _ => fail "iSpecialize:" H "should be a hypothesis, use iPoseProof instead"
    end
  | _ => fail "iSpecialize:" t "should be a proof mode term"
  end.

Tactic Notation "iSpecialize" open_constr(t) :=
  iSpecializeCore t as false.
Tactic Notation "iSpecialize" open_constr(t) "as" "#" :=
  iSpecializeCore t as true.

(** * Pose proof *)
(* The tactic [iIntoValid] tactic solves a goal [uPred_valid Q]. The
arguments [t] is a Coq term whose type is of the following shape:

- [∀ (x_1 : A_1) .. (x_n : A_n), uPred_valid Q]
- [∀ (x_1 : A_1) .. (x_n : A_n), P1 ⊢ P2], in which case [Q] becomes [P1 -∗ P2]
- [∀ (x_1 : A_1) .. (x_n : A_n), P1 ⊣⊢ P2], in which case [Q] becomes [P1 ↔ P2]

The tactic instantiates each dependent argument [x_i] with an evar and generates
a goal [P] for non-dependent arguments [x_i : P]. *)
Tactic Notation "iIntoValid" open_constr(t) :=
  let rec go t :=
    let tT := type of t in
    first
      [apply (proj1 (_ : AsValid tT _) t)
      |lazymatch eval hnf in tT with
       | ?P → ?Q => let H := fresh in assert P as H; [|go uconstr:(t H); clear H]
       | ∀ _ : ?T, _ =>
         (* Put [T] inside an [id] to avoid TC inference from being invoked. *)
         (* This is a workarround for Coq bug #4969. *)
         let e := fresh in evar (e:id T);
         let e' := eval unfold e in e in clear e; go (t e')
       end] in
  go t.

(* The tactic [tac] is called with a temporary fresh name [H]. The argument
[lazy_tc] denotes whether type class inference on the premises of [lem] should
be performed before (if false) or after (if true) [tac H] is called. *)
Tactic Notation "iPoseProofCore" open_constr(lem)
    "as" constr(p) constr(lazy_tc) tactic(tac) :=
  try iStartProof;
  let Htmp := iFresh in
  let t :=
    lazymatch lem with ITrm ?t ?xs ?pat => t | _ => lem end in
  let spec_tac _ :=
    lazymatch lem with
    | ITrm ?t ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as p
    | _ => idtac
    end in
  let go goal_tac :=
    lazymatch type of t with
    | string =>
       eapply tac_pose_proof_hyp with _ _ t _ Htmp _;
         [env_reflexivity || fail "iPoseProof:" t "not found"
         |env_reflexivity || fail "iPoseProof:" Htmp "not fresh"
         |goal_tac ()]
    | _ =>
       eapply tac_pose_proof with _ Htmp _; (* (j:=H) *)
         [iIntoValid t
         |env_reflexivity || fail "iPoseProof:" Htmp "not fresh"
         |goal_tac ()]
    end;
    try (apply _) in
  lazymatch eval compute in lazy_tc with
  | true => go ltac:(fun _ => spec_tac (); last (tac Htmp))
  | false => go spec_tac; last (tac Htmp)
  end.

(** * Apply *)
Tactic Notation "iApply" open_constr(lem) :=
  let rec go H := first
    [eapply tac_apply with _ H _ _ _;
      [env_reflexivity
      |apply _
      |lazy beta (* reduce betas created by instantiation *)]
    |iSpecializePat H "[]"; last go H] in
  iPoseProofCore lem as false true (fun H => first
    [iExact H
    |go H
    |lazymatch iTypeOf H with
     | Some (_,?Q) => fail 1 "iApply: cannot apply" Q
     end]).

(** * Revert *)
Local Tactic Notation "iForallRevert" ident(x) :=
  let err x :=
    intros x;
    iMatchHyp (fun H P =>
      lazymatch P with
      | context [x] => fail 2 "iRevert:" x "is used in hypothesis" H
      end) in
  let A := type of x in
  lazymatch type of A with
  | Prop => revert x; first [apply tac_pure_revert|err x]
  | _ => revert x; first [apply tac_forall_revert|err x]
  end.

Tactic Notation "iRevert" constr(Hs) :=
  let rec go Hs :=
    lazymatch Hs with
    | [] => idtac
    | ESelPure :: ?Hs =>
       repeat match goal with x : _ |- _ => revert x end;
       go Hs
    | ESelName _ ?H :: ?Hs =>
       eapply tac_revert with _ H _ _; (* (i:=H2) *)
         [env_reflexivity || fail "iRevert:" H "not found"
         |env_cbv; go Hs]
    end in
  let Hs := iElaborateSelPat Hs in go Hs.

Tactic Notation "iRevert" "(" ident(x1) ")" :=
  iForallRevert x1.
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" :=
  iForallRevert x2; iRevert ( x1 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" :=
  iForallRevert x3; iRevert ( x1 x2 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
  iForallRevert x4; iRevert ( x1 x2 x3 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" :=
  iForallRevert x5; iRevert ( x1 x2 x3 x4 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" :=
  iForallRevert x6; iRevert ( x1 x2 x3 x4 x5 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" :=
  iForallRevert x7; iRevert ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" :=
  iForallRevert x8; iRevert ( x1 x2 x3 x4 x5 x6 x7 ).

Tactic Notation "iRevert" "(" ident(x1) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 ).

(** * Disjunction *)
Tactic Notation "iLeft" :=
  iStartProof;
  eapply tac_or_l;
    [apply _ ||
     let P := match goal with |- FromOr ?P _ _ => P end in
     fail "iLeft:" P "not a disjunction"
    |].
Tactic Notation "iRight" :=
  iStartProof;
  eapply tac_or_r;
    [apply _ ||
     let P := match goal with |- FromOr ?P _ _ => P end in
     fail "iRight:" P "not a disjunction"
    |].

Local Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_or_destruct with _ _ H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [env_reflexivity || fail "iOrDestruct:" H "not found"
    |apply _ ||
     let P := match goal with |- IntoOr ?P _ _ => P end in
     fail "iOrDestruct: cannot destruct" P
    |env_reflexivity || fail "iOrDestruct:" H1 "not fresh"
    |env_reflexivity || fail "iOrDestruct:" H2 "not fresh"
    | |].

(** * Conjunction and separating conjunction *)
Tactic Notation "iSplit" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ _ =>
    eapply tac_and_split;
      [apply _ ||
       let P := match goal with |- FromAnd ?P _ _ => P end in
       fail "iSplit:" P "not a conjunction"| |]
  end.

Tactic Notation "iSplitL" constr(Hs) :=
  iStartProof;
  let Hs := words Hs in
  eapply tac_sep_split with _ _ false Hs _ _; (* (js:=Hs) *)
    [apply _ ||
     let P := match goal with |- FromSep _ ?P _ _ => P end in
     fail "iSplitL:" P "not a separating conjunction"
    |env_reflexivity ||
     let Hs := iMissingHyps Hs in
     fail "iSplitL: hypotheses" Hs "not found"
    | |].

Tactic Notation "iSplitR" constr(Hs) :=
  iStartProof;
  let Hs := words Hs in
  eapply tac_sep_split with _ _ true Hs _ _; (* (js:=Hs) *)
    [apply _ ||
     let P := match goal with |- FromSep _ ?P _ _ => P end in
     fail "iSplitR:" P "not a separating conjunction"
    |env_reflexivity ||
     let Hs := iMissingHyps Hs in
     fail "iSplitR: hypotheses" Hs "not found"
    | |].

Tactic Notation "iSplitL" := iSplitR "".
Tactic Notation "iSplitR" := iSplitL "".

Local Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_and_destruct with _ H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [env_reflexivity || fail "iAndDestruct:" H "not found"
    |apply _ ||
     let P := match goal with |- IntoSep _ ?P _ _ => P end in
     fail "iAndDestruct: cannot destruct" P
    |env_reflexivity || fail "iAndDestruct:" H1 "or" H2 " not fresh"|].

Local Tactic Notation "iAndDestructChoice" constr(H) "as" constr(lr) constr(H') :=
  eapply tac_and_destruct_choice with _ H _ lr H' _ _ _;
    [env_reflexivity || fail "iAndDestructChoice:" H "not found"
    |env_cbv; apply _ ||
     let P := match goal with |- Or (IntoAnd _ ?P _ _) _ => P end in
     fail "iAndDestructChoice: cannot destruct" P
    |env_reflexivity || fail "iAndDestructChoice:" H' " not fresh"|].

(** * Combinining hypotheses *)
Tactic Notation "iCombine" constr(Hs) "as" constr(H) :=
  let Hs := words Hs in
  eapply tac_combine with _ _ Hs _ _ H _;
    [env_reflexivity ||
     let Hs := iMissingHyps Hs in
     fail "iCombine: hypotheses" Hs "not found"
    |apply _
    |env_reflexivity || fail "iCombine:" H "not fresh"|].

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(H) :=
  iCombine [H1;H2] as H.

(** * Existential *)
Tactic Notation "iExists" uconstr(x1) :=
  iStartProof;
  eapply tac_exist;
    [apply _ ||
     let P := match goal with |- FromExist ?P _ => P end in
     fail "iExists:" P "not an existential"
    |cbv beta; eexists x1].

Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) :=
  iExists x1; iExists x2.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) :=
  iExists x1; iExists x2, x3.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) :=
  iExists x1; iExists x2, x3, x4.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) :=
  iExists x1; iExists x2, x3, x4, x5.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) :=
  iExists x1; iExists x2, x3, x4, x5, x6.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) ","
    uconstr(x8) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7, x8.

Local Tactic Notation "iExistDestruct" constr(H)
    "as" simple_intropattern(x) constr(Hx) :=
  eapply tac_exist_destruct with H _ Hx _ _; (* (i:=H) (j:=Hx) *)
    [env_reflexivity || fail "iExistDestruct:" H "not found"
    |apply _ ||
     let P := match goal with |- IntoExist ?P _ => P end in
     fail "iExistDestruct: cannot destruct" P|];
  let y := fresh in
  intros y; eexists; split;
    [env_reflexivity || fail "iExistDestruct:" Hx "not fresh"
    |revert y; intros x].

(** * Always *)
Tactic Notation "iAlways":=
  iStartProof;
  eapply tac_always_intro;
    [apply _ || fail "iAlways: the goal is not an always modality"
    |env_cbv].

(** * Later *)
Tactic Notation "iNext" open_constr(n) :=
  iStartProof;
  let P := match goal with |- _ ⊢ ?P => P end in
  try lazymatch n with 0 => fail 1 "iNext: cannot strip 0 laters" end;
  eapply (tac_next _ _ n);
    [apply _ || fail "iNext:" P "does not contain" n "laters"
    |lazymatch goal with
     | |- IntoLaterNEnvs 0 _ _ => fail "iNext:" P "does not contain laters"
     | _ => apply _
     end
    |lazy beta (* remove beta redexes caused by removing laters under binders*)].

Tactic Notation "iNext":= iNext _.

(** * Update modality *)
Tactic Notation "iModIntro" :=
  iStartProof;
  eapply tac_modal_intro;
    [apply _ ||
     let P := match goal with |- FromModal ?P _ => P end in
     fail "iModIntro:" P "not a modality"|].

Tactic Notation "iModCore" constr(H) :=
  eapply tac_modal_elim with _ H _ _ _ _;
    [env_reflexivity || fail "iMod:" H "not found"
    |apply _ ||
     let P := match goal with |- ElimModal ?P _ _ _ => P end in
     let Q := match goal with |- ElimModal _ _ ?Q _ => Q end in
     fail "iMod: cannot eliminate modality " P "in" Q
    |env_reflexivity|].

(** * Basic destruct tactic *)
Local Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
  let rec go Hz pat :=
    lazymatch pat with
    | IAnom => idtac
    | IDrop => iClear Hz
    | IFrame => iFrame Hz
    | IName ?y => iRename Hz into y
    | IList [[]] => iExFalso; iExact Hz
    | IList [[?pat1; IDrop]] => iAndDestructChoice Hz as true Hz; go Hz pat1
    | IList [[IDrop; ?pat2]] => iAndDestructChoice Hz as false Hz; go Hz pat2
    | IList [[?pat1; ?pat2]] =>
       let Hy := iFresh in iAndDestruct Hz as Hz Hy; go Hz pat1; go Hy pat2
    | IList [[?pat1];[?pat2]] => iOrDestruct Hz as Hz Hz; [go Hz pat1|go Hz pat2]
    | IPureElim => iPure Hz as ?
    | IAlwaysElim ?pat => iPersistent Hz; go Hz pat
    | IModalElim ?pat => iModCore Hz; go Hz pat
    | _ => fail "iDestruct:" pat "invalid"
    end in
  let rec find_pat found pats :=
    lazymatch pats with
    | [] =>
      lazymatch found with
      | true => idtac
      | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
      end
    | ISimpl :: ?pats => simpl; find_pat found pats
    | IClear ?H :: ?pats => iClear H; find_pat found pats
    | IClearFrame ?H :: ?pats => iFrame H; find_pat found pats
    | ?pat :: ?pats =>
       lazymatch found with
       | false => go H pat; find_pat true pats
       | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
       end
    end in
  let pats := intro_pat.parse pat in
  find_pat false pats.

Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as @ pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat.

(** * Introduction tactic *)
Tactic Notation "iIntros" constr(pat) :=
  let rec go pats :=
    lazymatch pats with
    | [] => idtac
    (* Optimizations to avoid generating fresh names *)
    | IPureElim :: ?pats => iIntro (?); go pats
    | IAlwaysElim (IName ?H) :: ?pats => iIntro #H; go pats
    | IDrop :: ?pats => iIntro _; go pats
    | IName ?H :: ?pats => iIntro H; go pats
    (* Introduction patterns that can only occur at the top-level *)
    | IPureIntro :: ?pats => iPureIntro; go pats
    | IAlwaysIntro :: ?pats => iAlways; go pats
    | IModalIntro :: ?pats => iModIntro; go pats
    | IForall :: ?pats => repeat iIntroForall; go pats
    | IAll :: ?pats => repeat (iIntroForall || iIntro); go pats
    (* Clearing and simplifying introduction patterns *)
    | ISimpl :: ?pats => simpl; go pats
    | IClear ?H :: ?pats => iClear H; go pats
    | IClearFrame ?H :: ?pats => iFrame H; go pats
    | IDone :: ?pats => try done; go pats
    (* Introduction + destruct *)
    | IAlwaysElim ?pat :: ?pats =>
       let H := iFresh in iIntro #H; iDestructHyp H as pat; go pats
    | ?pat :: ?pats =>
       let H := iFresh in iIntro H; iDestructHyp H as pat; go pats
    end
  in let pats := intro_pat.parse pat in go pats.
Tactic Notation "iIntros" := iIntros [IAll].

Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" :=
  iIntro ( x1 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" :=
  iIntros ( x1 ); iIntro ( x2 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" :=
  iIntros ( x1 x2 ); iIntro ( x3 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) ")" :=
  iIntros ( x1 x2 x3 ); iIntro ( x4 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) ")" :=
  iIntros ( x1 x2 x3 x4 ); iIntro ( x5 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) ")" :=
  iIntros ( x1 x2 x3 x4 x5 ); iIntro ( x6 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 ); iIntro ( x7 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntro ( x8 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntro ( x9 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntro ( x10 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntro ( x11 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntro ( x12 ).

Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" constr(p) :=
  iIntros ( x1 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    ")" constr(p) :=
  iIntros ( x1 x2 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" constr(p) :=
  iIntros ( x1 x2 x3 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntros p.

Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1) ")" :=
  iIntros p; iIntros ( x1 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" :=
  iIntros p; iIntros ( x1 x2 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" :=
  iIntros p; iIntros ( x1 x2 x3 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ).

Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1) ")" constr(p2) :=
  iIntros p; iIntros ( x1 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntros p2.


(* Used for generalization in iInduction and iLöb *)
Tactic Notation "iRevertIntros" constr(Hs) "with" tactic(tac) :=
  let rec go Hs :=
    lazymatch Hs with
    | [] => tac
    | ESelPure :: ?Hs => fail "iRevertIntros: % not supported"
    | ESelName ?p ?H :: ?Hs =>
       iRevert H; go Hs;
       let H' :=
         match p with true => constr:([IAlwaysElim (IName H)]) | false => H end in
       iIntros H'
    end in
  try iStartProof; let Hs := iElaborateSelPat Hs in go Hs.

Tactic Notation "iRevertIntros" "(" ident(x1) ")" constr(Hs) "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1); tac; iIntros (x1)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ")" constr(Hs)
    "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2); tac; iIntros (x1 x2)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs)
    "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3); tac; iIntros (x1 x2 x3)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    constr(Hs) "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4); tac; iIntros (x1 x2 x3 x4)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" constr(Hs) "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5); tac; iIntros (x1 x2 x3 x4 x5)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" constr(Hs) "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6);
    tac; iIntros (x1 x2 x3 x4 x5 x6)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" constr(Hs) "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) "with" tactic(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8)).

Tactic Notation "iRevertIntros" "with" tactic(tac) :=
  iRevertIntros "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ")" "with" tactic(tac):=
  iRevertIntros (x1) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ")" "with" tactic(tac):=
  iRevertIntros (x1 x2) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ")"
    "with" tactic(tac):=
  iRevertIntros (x1 x2 x3) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    "with" tactic(tac):=
  iRevertIntros (x1 x2 x3 x4) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" "with" tactic(tac):=
  iRevertIntros (x1 x2 x3 x4 x5) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" "with" tactic(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" "with" tactic(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" "with" tactic(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with tac.

(** * Destruct tactic *)
Class CopyDestruct {PROP : bi} (P : PROP).
Arguments CopyDestruct {_} _%I.
Hint Mode CopyDestruct + ! : typeclass_instances.

Instance copy_destruct_forall {PROP : bi} {A} (Φ : A → PROP) : CopyDestruct (∀ x, Φ x).
Instance copy_destruct_impl {PROP : bi} (P Q : PROP) :
  CopyDestruct Q → CopyDestruct (P → Q).
Instance copy_destruct_wand {PROP : bi} (P Q : PROP) :
  CopyDestruct Q → CopyDestruct (P -∗ Q).
Instance copy_destruct_bare {PROP : bi} (P : PROP) :
  CopyDestruct P → CopyDestruct (■ P).
Instance copy_destruct_always {PROP : bi} (P : PROP) :
  CopyDestruct P → CopyDestruct (□ P).

Tactic Notation "iDestructCore" open_constr(lem) "as" constr(p) tactic(tac) :=
  let hyp_name :=
    lazymatch type of lem with
    | string => constr:(Some lem)
    | iTrm =>
       lazymatch lem with
       | @iTrm string ?H _ _ => constr:(Some H) | _ => constr:(@None string)
       end
    | _ => constr:(@None string)
    end in
  let intro_destruct n :=
    let rec go n' :=
      lazymatch n' with
      | 0 => fail "iDestruct: cannot introduce" n "hypotheses"
      | 1 => repeat iIntroForall; let H := iFresh in iIntro H; tac H
      | S ?n' => repeat iIntroForall; let H := iFresh in iIntro H; go n'
      end in
    intros; iStartProof; go n in
  lazymatch type of lem with
  | nat => intro_destruct lem
  | Z => (* to make it work in Z_scope. We should just be able to bind
     tactic notation arguments to notation scopes. *)
     let n := eval compute in (Z.to_nat lem) in intro_destruct n
  | _ =>
     (* Only copy the hypothesis in case there is a [CopyDestruct] instance.
     Also, rule out cases in which it does not make sense to copy, namely when
     destructing a lemma (instead of a hypothesis) or a spatial hyopthesis
     (which cannot be kept). *)
     lazymatch hyp_name with
     | None => iPoseProofCore lem as p false tac
     | Some ?H =>
        lazymatch iTypeOf H with
        | None => fail "iDestruct:" H "not found"
        | Some (true, ?P) =>
           (* persistent hypothesis, check for a CopyDestruct instance *)
           tryif (let dummy := constr:(_ : CopyDestruct P) in idtac)
           then (iPoseProofCore lem as p false tac)
           else (iSpecializeCore lem as p; last (tac H))
        | Some (false, ?P) =>
           (* spatial hypothesis, cannot copy *)
           iSpecializeCore lem as p; last (tac H)
        end
     end
  end.

Tactic Notation "iDestruct" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Tactic Notation "iDestruct" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as true (fun H => iPure H as pat).

Tactic Notation "iPoseProof" open_constr(lem) "as" constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iPoseProofCore lem as pat false (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

(** * Induction *)
(* An invocation of [iInduction (x) as pat IH forall (x1...xn) Hs] will
result in the following actions:

- Revert the proofmode hypotheses [Hs]
- Revert all remaining spatial hypotheses and the remaining persistent
  hypotheses containing the induction variable [x]
- Revert the pure hypotheses [x1..xn]

- Actuall perform induction

- Introduce thee pure hypotheses [x1..xn]
- Introduce the spatial hypotheses and persistent hypotheses involving [x]
- Introduce the proofmode hypotheses [Hs]
*)
Tactic Notation "iInductionCore" constr(x) "as" simple_intropattern(pat) constr(IH) :=
  let rec fix_ihs :=
    lazymatch goal with
    | H : coq_tactics.of_envs _ ⊢ _ |- _ =>
       eapply tac_revert_ih;
         [reflexivity || fail "iInduction: spatial context not empty, this should not happen"
         |apply H|];
       clear H; fix_ihs;
       let IH' := iFresh' IH in iIntros [IAlwaysElim (IName IH')]
    | _ => idtac
    end in
  induction x as pat; fix_ihs.

Ltac iHypsContaining x :=
  let rec go Γ x Hs :=
    lazymatch Γ with
    | Enil => constr:(Hs)
    | Esnoc ?Γ ?H ?Q =>
       match Q with
       | context [x] => go Γ x (H :: Hs)
       | _ => go Γ x Hs
       end
     end in
  let Γp := lazymatch goal with |- of_envs (Envs ?Γp _) ⊢ _ => Γp end in
  let Γs := lazymatch goal with |- of_envs (Envs _ ?Γs) ⊢ _ => Γs end in
  let Hs := go Γp x (@nil string) in go Γs x Hs.

Tactic Notation "iInductionRevert" constr(x) constr(Hs) "with" tactic(tac) :=
  iRevertIntros Hs with (
    iRevertIntros "∗" with (
      idtac;
      let Hsx := iHypsContaining x in
      iRevertIntros Hsx with tac
    )
  ).

Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) :=
  iInductionRevert x "" with (iInductionCore x as pat IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2 x3) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2 x3 x4) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2 x3 x4 x5) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2 x3 x4 x5 x6) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ")" :=
  iInductionRevert x "" with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7 x8) "" with (iInductionCore x as pat IH)).

Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" constr(Hs) :=
  iInductionRevert x Hs with (iInductionCore x as pat IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ")" constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ")" constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2 x3) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2 x3 x4) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ")"
    constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2 x3 x4 x5) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ")"
    constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2 x3 x4 x5 x6) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ")" constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7) "" with (iInductionCore x as pat IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ")" constr(Hs) :=
  iInductionRevert x Hs with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7 x8) "" with (iInductionCore x as pat IH)).

(** * Löb Induction *)
Tactic Notation "iLöbCore" "as" constr (IH) :=
  iStartProof;
  eapply tac_löb with _ IH;
    [reflexivity || fail "iLöb: spatial context not empty, this should not happen"
    |env_reflexivity || fail "iLöb:" IH "not fresh"|].

Tactic Notation "iLöbRevert" constr(Hs) "with" tactic(tac) :=
  iRevertIntros Hs with (
    iRevertIntros "∗" with tac
  ).

Tactic Notation "iLöb" "as" constr (IH) :=
  iLöbRevert "" with (iLöbCore as IH).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ")" :=
  iLöbRevert "" with (iRevertIntros(x1) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2 x3) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2 x3 x4) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2 x3 x4 x5) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2 x3 x4 x5 x6) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ")" :=
  iLöbRevert "" with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7 x8) "" with (iLöbCore as IH)).

Tactic Notation "iLöb" "as" constr (IH) "forall" constr(Hs) :=
  iLöbRevert Hs with (iLöbCore as IH).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2) ")"
    constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2 x3) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2 x3 x4) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2 x3 x4 x5) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2 x3 x4 x5 x6) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros(x1 x2 x3 x4 x5 x6 x7 x8) "" with (iLöbCore as IH)).

(** * Assert *)
(* The argument [p] denotes whether [Q] is persistent. It can either be a
Boolean or an introduction pattern, which will be coerced into [true] if it
only contains `#` or `%` patterns at the top-level, and [false] otherwise. *)
Tactic Notation "iAssertCore" open_constr(Q)
    "with" constr(Hs) "as" constr(p) tactic(tac) :=
  iStartProof;
  let p := intro_pat_persistent p in
  let H := iFresh in
  let Hs := spec_pat.parse Hs in
  lazymatch Hs with
  | [SPureGoal ?d] =>
     eapply tac_assert_pure with _ H Q _;
       [env_reflexivity
       |apply _ || fail "iAssert:" Q "not pure"
       |apply _
       |done_if d (*goal*)
       |tac H]
  | [SGoal (SpecGoal GPersistent _ ?Hs_frame [] ?d)] =>
     eapply tac_assert_persistent with _ _ _ true [] H Q _;
       [env_reflexivity
       |apply _ || fail "iAssert:" Q "not persistent"
       |apply _
       |env_reflexivity
       |iFrame Hs_frame; done_if d (*goal*)
       |tac H]
  | [SGoal (SpecGoal GPersistent false ?Hs_frame _ ?d)] =>
     fail "iAssert: cannot select hypotheses for persistent proposition"
  | [SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if lr then Hs else Hs_frame ++ Hs) in
     let p' := eval cbv in (match m with GModal => false | _ => p end) in
     lazymatch p' with
     | false =>
       eapply tac_assert with _ _ _ lr Hs' H Q _;
         [lazymatch m with
          | GSpatial => apply elim_modal_dummy
          | GModal => apply _ || fail "iAssert: goal not a modality"
          end
         |env_reflexivity ||
          let Hs' := iMissingHyps Hs' in
          fail "iAssert: hypotheses" Hs' "not found"
         |env_reflexivity
         |iFrame Hs_frame; done_if d (*goal*)
         |tac H]
     | true =>
       eapply tac_assert_persistent with _ _ _ lr Hs' H Q _;
         [env_reflexivity ||
          let Hs' := iMissingHyps Hs' in
          fail "iAssert: hypotheses" Hs' "not found"
         |apply _ || fail "iAssert:" Q "not persistent"
         |apply _
         |env_reflexivity
         |done_if d (*goal*)
         |tac H]
     end
  | ?pat => fail "iAssert: invalid pattern" pat
  end.

Tactic Notation "iAssertCore" open_constr(Q) "as" constr(p) tactic(tac) :=
  let p := intro_pat_persistent p in
  lazymatch p with
  | true => iAssertCore Q with "[#]" as p tac
  | false => iAssertCore Q with "[]" as p tac
  end.

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1) pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1 x2) pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1 x2 x3) pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1 x2 x3 x4) pat).

Tactic Notation "iAssert" open_constr(Q) "as" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1) pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1 x2) pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1 x2 x3) pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1 x2 x3 x4) pat).

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs)
    "as" "%" simple_intropattern(pat) :=
  iAssertCore Q with Hs as true (fun H => iPure H as pat).
Tactic Notation "iAssert" open_constr(Q) "as" "%" simple_intropattern(pat) :=
  iAssert Q with "[-]" as %pat.

(** * Rewrite *)
Local Ltac iRewriteFindPred :=
  match goal with
  | |- _ ⊣⊢ ?Φ ?x =>
     generalize x;
     match goal with |- (∀ y, @?Ψ y ⊣⊢ _) => unify Φ Ψ; reflexivity end
  end.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) :=
  iPoseProofCore lem as true true (fun Heq =>
    eapply (tac_rewrite _ Heq _ _ lr);
      [env_reflexivity || fail "iRewrite:" Heq "not found"
      |apply _ ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity|lazy beta; iClear Heq]).

Tactic Notation "iRewrite" open_constr(lem) := iRewriteCore false lem.
Tactic Notation "iRewrite" "-" open_constr(lem) := iRewriteCore true lem.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) "in" constr(H) :=
  iPoseProofCore lem as true true (fun Heq =>
    eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
      [env_reflexivity || fail "iRewrite:" Heq "not found"
      |env_reflexivity || fail "iRewrite:" H "not found"
      |apply _ ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity
      |env_reflexivity|lazy beta; iClear Heq]).

Tactic Notation "iRewrite" open_constr(lem) "in" constr(H) :=
  iRewriteCore false lem in H.
Tactic Notation "iRewrite" "-" open_constr(lem) "in" constr(H) :=
  iRewriteCore true lem in H.

Ltac iSimplifyEq := repeat (
  iMatchHyp (fun H P => match P with ⌜_ = _⌝%I => iDestruct H as %? end)
  || simplify_eq/=).

(** * Update modality *)
Tactic Notation "iMod" open_constr(lem) :=
  iDestructCore lem as false (fun H => iModCore H).
Tactic Notation "iMod" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as ( x1 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Tactic Notation "iMod" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as false (fun H => iModCore H; iPure H as pat).

(* Make sure that by and done solve trivial things in proof mode *)
Hint Extern 0 (of_envs _ ⊢ _) => by iPureIntro.
Hint Extern 0 (of_envs _ ⊢ _) => iAssumption.
Hint Extern 0 (of_envs _ ⊢ emp) => iEmpIntro.
Hint Resolve bi.internal_eq_refl. (* Maybe make an [iReflexivity] tactic *)

(* For iIntros we do not check whether we are in proof mode because we actually
want it to enter proof mode when we are not already in it. *)
Hint Extern 0 (_ ⊢ _) => progress iIntros.

Hint Extern 1 (of_envs _ ⊢ _ ∧ _) => iSplit.
Hint Extern 1 (of_envs _ ⊢ _ ∗ _) => iSplit.
Hint Extern 1 (of_envs _ ⊢ ▷ _) => iNext.
Hint Extern 1 (of_envs _ ⊢ □ _) => iAlways.
Hint Extern 1 (of_envs _ ⊢ ∃ _, _) => iExists _.
Hint Extern 1 (of_envs _ ⊢ ◇ _) => iModIntro.
Hint Extern 1 (of_envs _ ⊢ _ ∨ _) => iLeft.
Hint Extern 1 (of_envs _ ⊢ _ ∨ _) => iRight.

Hint Extern 2 (of_envs _ ⊢ _ ∗ _) => progress iFrame : iFrame.
