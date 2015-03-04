Require Import ssreflect.
Require Import world_prop core_lang masks iris_core iris_plog.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_VS_RULES (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  Implicit Types (P Q R : Props) (w : Wld) (n i k : nat) (m : mask) (r : res) (σ : state).

  Section ViewShiftProps.

    Lemma vsTimeless m P :
      timeless P ⊑ vs m m (▹P) P.
    Proof.
      intros w' n r1 HTL w HSub; rewrite ->HSub in HTL; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp; split; [reflexivity | split; [| assumption] ]; clear HE HD.
      destruct np as [| np]; [now inversion HLe0 |]; simpl in Hp.
      unfold lt in HLe0; rewrite ->HLe0.
      rewrite <- HSub; apply HTL, Hp; [reflexivity | assumption].
    Qed.

    Lemma vsOpen i P :
      valid (vs (mask_sing i) mask_emp (inv i P) (▹P)).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HInv w'; clear nn; intros.
      change (match w i with Some x => x = S n = ı' P | None => False end) in HInv.
      destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite ->(isoR P) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [rs [HE HM] ].
      destruct (rs i) as [ri |] eqn: HLr.
      - rewrite ->comp_map_remove with (i := i) (r := ri) in HE by now eapply equivR.
        rewrite ->assoc, <- (assoc r), (comm rf), assoc in HE.
        exists w' (r · ri).
        split; [reflexivity |].
        split.
        + simpl; eapply HInv; [now auto with arith |].
          eapply uni_pred, HM with i;
            [| exists r | | | rewrite HLr]; try reflexivity.
          * left; unfold mask_sing, mask_set.
            destruct (Peano_dec.eq_nat_dec i i); tauto.
          * specialize (HSub i); rewrite HLu in HSub.
            symmetry; destruct (w' i); [assumption | contradiction].
        + exists (fdRemove i rs); split; [assumption | intros j Hm].
          destruct Hm as [| Hm]; [contradiction |]; specialize (HD j); simpl in HD.
          unfold mask_sing, mask_set, mcup in HD; destruct (Peano_dec.eq_nat_dec i j);
          [subst j; contradiction HD; tauto | clear HD].
          rewrite fdLookup_in; setoid_rewrite (fdRemove_neq _ _ _ n0); rewrite <- fdLookup_in; unfold mcup in HM; now auto.
      - rewrite <- fdLookup_notin_strong in HLr; contradiction HLr; clear HLr.
        specialize (HSub i); rewrite HLu in HSub; clear - HM HSub.
        destruct (HM i) as [HD _]; [left | rewrite ->HD, fdLookup_in_strong; destruct (w' i); [eexists; reflexivity | contradiction] ].
        clear; unfold mask_sing, mask_set.
        destruct (Peano_dec.eq_nat_dec i i); tauto.
    Qed.

    Lemma vsClose i P :
      valid (vs mask_emp (mask_sing i) (inv i P * ▹P) ⊤).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ [r1 [r2 [HR [HInv HP] ] ] ] w'; clear nn; intros.
      change (match w i with Some x => x = S n = ı' P | None => False end) in HInv.
      destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite ->(isoR P) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [rs [HE HM] ].
      exists w' 1; split; [reflexivity | split; [exact I |] ].
      rewrite ->(comm r), <-assoc in HE.
      remember (match rs i with Some ri => ri | None => 1 end) as ri eqn: EQri.
      pose (rri := (ri · r)).
      exists (fdUpdate i rri rs); split; [| intros j Hm].
      - simpl. erewrite ra_op_unit by apply _.
        clear - HE EQri. destruct (rs i) as [rsi |] eqn: EQrsi.
        + subst rsi. erewrite <-comp_map_insert_old; [ eassumption | eapply equivR; eassumption | reflexivity ].
        + unfold rri. subst ri. simpl. erewrite <-comp_map_insert_new; [|now eapply equivR]. simpl.
          erewrite ra_op_unit by apply _. assumption.
      - specialize (HD j); unfold mask_sing, mask_set, mcup in *; simpl in Hm, HD.
        destruct (Peano_dec.eq_nat_dec i j);
          [subst j; clear Hm |
           destruct Hm as [Hm | Hm]; [contradiction | rewrite ->fdLookup_in_strong, fdUpdate_neq, <- fdLookup_in_strong by assumption; now auto] ].
        rewrite ->!fdLookup_in_strong, fdUpdate_eq.
        destruct n as [| n]; [now inversion HLe | simpl in HP].
        rewrite ->HSub in HP; specialize (HSub i); rewrite HLu in HSub.
        destruct (w' i) as [π' |]; [| contradiction].
        split; [intuition now eauto | intros].
        simpl in HLw, HSub. change (rri == ri0) in HLrs. rewrite <- HLw, <- HSub.
        apply HInv; [now auto with arith |].
        eapply uni_pred, HP; [now auto with arith |].
        rewrite <-HLrs. clear dependent ri0.
        exists (ri · r1).
        subst rri. rewrite <-HR, assoc. reflexivity.
    Qed.

    Lemma vsTrans P Q R m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 P Q ∧ vs m2 m3 Q R ⊑ vs m1 m3 P R.
    Proof.
      intros w' n r1 [Hpq Hqr] w HSub; specialize (Hpq _ HSub); rewrite ->HSub in Hqr; clear w' HSub.
      intros np rp HLe HS Hp w1; intros; specialize (Hpq _ _ HLe HS Hp).
      edestruct Hpq as [w2 [rq [HSw12 [Hq HEq] ] ] ]; try eassumption; [|].
      { clear - HD HMS; intros j [Hmf Hm12]; apply (HD j); split; [assumption |].
        destruct Hm12 as [Hm1 | Hm2]; [left; assumption | apply HMS, Hm2].
      }
      rewrite <- HLe, HSub in Hqr; specialize (Hqr _ HSw12); clear Hpq HE w HSub Hp.
      edestruct (Hqr (S k) _ HLe0 (unit_min _) Hq w2) as [w3 [rR [HSw23 [Hr HEr] ] ] ];
        try (reflexivity || eassumption); [now auto with arith | |].
      { clear - HD HMS; intros j [Hmf Hm23]; apply (HD j); split; [assumption |].
        destruct Hm23 as [Hm2 | Hm3]; [apply HMS, Hm2 | right; assumption].
      }
      clear HEq Hq HS.
      setoid_rewrite HSw12; eauto 8.
    Qed.

    Lemma vsEnt P Q m :
      □(P → Q) ⊑ vs m m P Q.
    Proof.
      intros w' n r1 Himp w HSub; rewrite ->HSub in Himp; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp; split; [reflexivity | split; [| assumption ] ].
      eapply Himp; [assumption | now eauto with arith | now apply unit_min | ].
      unfold lt in HLe0; rewrite ->HLe0, <- HSub; assumption.
    Qed.

    Lemma vsFrame P Q R m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      vs m1 m2 P Q ⊑ vs (m1 ∪ mf) (m2 ∪ mf) (P * R) (Q * R).
    Proof.
      intros w' n r1 HVS w HSub; specialize (HVS _ HSub); clear w' r1 HSub.
      intros np rpr HLe _ [rp [rr [HR [Hp Hr] ] ] ] w'; intros.
      assert (HS : ra_unit _ ⊑ rp) by (eapply unit_min).
      specialize (HVS _ _ HLe HS Hp w' (rr · rf) (mf ∪ mf0) σ k); clear HS.
      destruct HVS as [w'' [rq [HSub' [Hq HEq] ] ] ]; try assumption; [| |].
      - (* disjointness of masks: possible lemma *)
        clear - HD HDisj; intros i [ [Hmf | Hmf] Hm12]; [eapply HDisj; now eauto |].
        unfold mcup in *; eapply HD; split; [eassumption | tauto].
      - rewrite ->assoc, HR; eapply wsat_equiv, HE; try reflexivity; [].
        clear; intros i; unfold mcup; tauto.
      - rewrite ->assoc in HEq.
        exists w'' (rq · rr).
        split; [assumption | split].
        + unfold lt in HLe0; rewrite ->HSub, HSub', <- HLe0 in Hr; exists rq rr.
          split; now auto.
        + eapply wsat_equiv, HEq; try reflexivity; [].
          clear; intros i; unfold mcup; tauto.
    Qed.

    Instance LP_res (P : RL.res -> Prop) : LimitPreserving P.
    Proof.
      intros σ σc HPc; simpl. unfold discreteCompl.
      now auto.
    Qed.

    Definition ownLP (P : RL.res -> Prop) : {s : RL.res | P s} -n> Props :=
      ownL <M< inclM.

    Lemma vsGhostUpd m rl (P : RL.res -> Prop)
          (HU : forall rf (HD : ↓(rl · rf)), exists sl, P sl /\ ↓(sl · rf)) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      unfold ownLP; intros _ _ _ w _ n [rp' rl'] _ _ HG w'; intros.
      destruct HE as [rs [ Hsat HE] ]. rewrite <-assoc in Hsat. destruct Hsat as [Hval Hst].
      destruct HG as [ [rdp rdl] [_ EQrl] ]. simpl in EQrl. clear rdp.
      destruct (HU (rdl · snd(rf · comp_map rs))) as [rsl [HPrsl HCrsl] ].
      - clear - Hval EQrl. eapply ra_prod_valid in Hval. destruct Hval as [_ Hsnd].
        rewrite ->assoc, (comm rl), EQrl.
        rewrite ra_op_prod_snd in Hsnd. exact Hsnd.
      - exists w' (rp', rsl).
        split; first reflexivity. split.
        + exists (exist _ rsl HPrsl). simpl.
          exists (rp', 1:RL.res). simpl.
          rewrite ra_op_unit ra_op_unit2. split; reflexivity.
        + exists rs. split; [| assumption]; clear HE. rewrite <-assoc. split; [eapply ra_prod_valid; split|].
          * clear - Hval. eapply ra_prod_valid in Hval. destruct Hval as [Hfst _].
            rewrite ra_op_prod_fst in Hfst.
            rewrite ra_op_prod_fst. exact Hfst.
          * clear -HCrsl. rewrite ->!assoc, (comm rsl), <-assoc in HCrsl.
            apply ra_op_valid2 in HCrsl. rewrite ra_op_prod_snd. exact HCrsl.
          * clear -Hst. rewrite ra_op_prod_fst. rewrite ra_op_prod_fst in Hst. exact Hst.
    Qed.

    Program Definition inv' m : Props -n> {n : nat | m n} -n> Props :=
      n[(fun P => n[(fun n : {n | m n} => inv n P)])].
    Next Obligation.
      intros i i' EQi; destruct n as [| n]; [apply dist_bound |].
      simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros p1 p2 EQp i; simpl morph.
      apply (inv (` i)); assumption.
    Qed.

    Lemma fresh_region (w : Wld) m (HInf : mask_infinite m) :
      exists i, m i /\ w i = None.
    Proof.
      destruct (HInf (S (List.last (dom w) 0%nat))) as [i [HGe Hm] ];
      exists i; split; [assumption |]; clear - HGe.
      rewrite <- fdLookup_notin_strong.
      destruct w as [ [| [n v] w] wP]; unfold dom in *; simpl findom_t in *; [tauto |].
      simpl List.map in *; rewrite last_cons in HGe.
      unfold ge in HGe; intros HIn; eapply Gt.gt_not_le, HGe.
      apply Le.le_n_S, SS_last_le; assumption.
    Qed.

    Instance LP_mask m : LimitPreserving m.
    Proof.
      intros σ σc Hp; apply Hp.
    Qed.

    Lemma vsNewInv P m (HInf : mask_infinite m) :
      valid (vs m m (▹P) (xist (inv' m P))).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HP w'; clear nn; intros.
      destruct n as [| n]; [now inversion HLe | simpl in HP].
      rewrite ->HSub in HP; clear w HSub; rename w' into w.
      destruct (fresh_region w m HInf) as [i [Hm HLi] ].
      assert (HSub : w ⊑ fdUpdate i (ı' P) w).
      { intros j; destruct (Peano_dec.eq_nat_dec i j); [subst j; rewrite HLi; exact I|].
        now rewrite ->fdUpdate_neq by assumption.
      }
      exists (fdUpdate i (ı' P) w) 1; split; [assumption | split].
      - exists (exist _ i Hm).
        change (((fdUpdate i (ı' P) w) i) = S (S k) = (Some (ı' P))).
        rewrite fdUpdate_eq; reflexivity.
      - erewrite ra_op_unit by apply _.
        destruct HE as [rs [HE HM] ].
        exists (fdUpdate i r rs).
        assert (HRi : rs i = None).
        { destruct (HM i) as [HDom _]; unfold mcup; [tauto |].
          rewrite <- fdLookup_notin_strong, HDom, fdLookup_notin_strong; assumption.
        }
        split.
        {
          rewrite <-comp_map_insert_new by now eapply equivR.
          rewrite ->assoc, (comm rf). assumption.
        }
        intros j Hm'.
        rewrite !fdLookup_in_strong; destruct (Peano_dec.eq_nat_dec i j).
        + subst j; rewrite !fdUpdate_eq; split; [intuition now eauto | intros].
          simpl in HLw. do 3 red in HLrs. rewrite <- HLw, isoR, <- HSub.
          eapply uni_pred, HP; [now auto with arith |]. rewrite HLrs. reflexivity.
        + rewrite ->!fdUpdate_neq, <- !fdLookup_in_strong by assumption.
          setoid_rewrite <- HSub.
          apply HM; assumption.
    Qed.

    Lemma vsNotOwnInvalid m1 m2 r
      (Hnval: ~↓r):
      valid (vs m1 m2 (ownR r) ⊥).
    Proof.
      intros pw n s w _. clear pw s.
      intros m s _ _. clear n.
      intros [rs Heq] w' rf mf σ k _ _ _ [ ri [ [ Hval _ ] ] ].
      exfalso.
      apply Hnval. rewrite <-Heq in Hval.
      eapply ra_op_valid2, ra_op_valid, ra_op_valid; last eassumption; now apply _.
    Qed.

  End ViewShiftProps.

End IRIS_VS_RULES.

Module IrisVSRules (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE): IRIS_VS_RULES RL C R WP CORE PLOG.
  Include IRIS_VS_RULES RL C R WP CORE PLOG.
End IrisVSRules.
