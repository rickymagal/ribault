From Coq Require Import String ZArith List Bool Arith Lia.
Import ListNotations.
From Ribault Require Import Syntax Interp Dfg Trans TransFacts.
Local Open Scope string_scope.

(* LIFT: evaluating a node that precedes a sub-translation is invariant under
   that sub-translation. Packages trans_fresh + eval_dfg_extend. *)
Lemma eval_dfg_trans_stable :
  forall e k ns es rho k' ns' es' out denv m p fuel,
    trans k ns es rho e = (k', ns', es', out) ->
    nodes_below ns k -> edges_below es k -> cenv_below rho k ->
    m < k ->
    eval_dfg fuel {| dnodes := ns; dedges := es |} denv m p
    = eval_dfg fuel {| dnodes := ns'; dedges := es' |} denv m p.
Proof.
  intros e k ns es rho k' ns' es' out denv m p fuel Htr Hn He Hc Hm.
  destruct (trans_fresh e k ns es rho k' ns' es' out Htr Hn He Hc)
    as [_ [_ [_ [_ [ [nx [Hns Hnx]] [ex [Hes Hex]] ] ]]]].
  subst ns' es'.
  apply eval_dfg_extend with (b := k).
  - exact He.
  - intros i nd Hin. destruct (Hnx i nd Hin) as [Hlo _]. exact Hlo.
  - intros s sp t tp Hin. destruct (Hex s sp t tp Hin) as [Hlo _]. exact Hlo.
  - exact Hm.
Qed.

(* The invariant survives extending rho and senv with a consistent binding:
   node i computes, in (ns,es), the value senv now holds for x. *)
Lemma env_inv_bind : forall rho senv denv ns es x i a fd,
  env_inv rho senv denv ns es ->
  eval_dfg fd {| dnodes := ns; dedges := es |} denv i "0" = Ok a ->
  env_inv ((x, i) :: rho) ((x, a) :: senv) denv ns es.
Proof.
  intros rho senv denv ns es x i a fd [Hfree Hbound] Hev.
  split.
  - intros y Hcl. cbn in Hcl.
    destruct (String.eqb y x) eqn:E; [discriminate Hcl|].
    cbn. rewrite E. apply Hfree. exact Hcl.
  - intros y j Hcl. cbn in Hcl.
    destruct (String.eqb y x) eqn:E.
    + inversion Hcl; subst. exists a, fd. split.
      * cbn. rewrite E. reflexivity.
      * exact Hev.
    + destruct (Hbound y j Hcl) as [v' [fd' [Hv' Hev']]].
      exists v', fd'. split.
      * cbn. rewrite E. exact Hv'.
      * exact Hev'.
Qed.

(* one evaluation step of the unary node trans builds for EUn *)
Lemma eval_dfg_un_step : forall fd k1 u ns1 o1 es1 denv,
  eval_dfg (S fd) {| dnodes := (k1, DUn u) :: ns1;
                     dedges := (o1, oport, k1, "0") :: es1 |} denv k1 "0"
  = rbind (eval_dfg fd {| dnodes := (k1, DUn u) :: ns1;
                          dedges := (o1, oport, k1, "0") :: es1 |} denv o1 oport)
          (fun a => eval_un u a).
Proof. intros. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

(* one evaluation step of the binary node trans builds for EBin *)
Lemma eval_dfg_bin_step : forall fd k2 o ns2 o1 o2 es2 denv,
  let G := {| dnodes := (k2, DBin o) :: ns2;
              dedges := (o1, oport, k2, "0") :: (o2, oport, k2, "1") :: es2 |} in
  eval_dfg (S fd) G denv k2 "0"
  = rbind (eval_dfg fd G denv o1 oport)
          (fun a => rbind (eval_dfg fd G denv o2 oport) (fun b => eval_bin o a b)).
Proof. intros. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

(* the fresh-prefix hypotheses of eval_dfg_extend for a one-node,
   few-edge top-level addition at id k *)
Lemma single_node_fresh : forall (k : nodeid) (nd : node) (i : nodeid) (nd' : node),
  In (i, nd') [(k, nd)] -> k <= i.
Proof. intros k nd i nd' [H|[]]. inversion H; lia. Qed.

(* PRESERVATION IN Ok (general): if the source evaluates e to Ok v under senv,
   and the invariant relates rho/denv to senv on the INPUT graph (ns,es),
   then the OUTPUT graph (ns',es') evaluates the output node to Ok v,
   with enough fuel. *)
Theorem trans_agree :
  forall e k ns es rho k' ns' es' out senv denv prog,
    trans k ns es rho e = (k', ns', es', out) ->
    straight_line e = true ->
    nodes_below ns k -> edges_below es k -> cenv_below rho k ->
    env_inv rho senv denv ns es ->
    forall fe v,
      eval fe prog senv e = Ok v ->
      exists fd, eval_dfg fd {| dnodes := ns'; dedges := es' |} denv out "0" = Ok v.
Proof.
  intros e. induction e; intros k ns es rho k' ns' es' out senv denv prog
                                 Htr Hsl Hn He Hc [Hfree Hbound] fe v Hev;
    cbn in Htr; (destruct fe as [|fe]; [cbn in Hev; discriminate Hev|]); cbn in Hev;
    cbn in Hsl.
  - (* EInt *)
    inversion Htr; subst. inversion Hev; subst v.
    exists 1. cbn. rewrite Nat.eqb_refl. reflexivity.
  - (* EBool *)
    inversion Htr; subst. inversion Hev; subst v.
    exists 1. cbn. rewrite Nat.eqb_refl. reflexivity.
  - (* EVar *)
    destruct (vlookup senv x) as [v0|] eqn:Ev; [|discriminate Hev].
    inversion Hev; subst v0.
    destruct (clookup rho x) as [i|] eqn:Ecl.
    + injection Htr as <- <- <- <-.
      destruct (Hbound x i Ecl) as [v' [fd [Hv' Hev']]].
      rewrite Ev in Hv'. inversion Hv'; subst v'.
      exists fd. exact Hev'.
    + inversion Htr; subst.
      pose proof (Hfree x Ecl) as Hfx.
      exists 1. cbn. rewrite Nat.eqb_refl. rewrite <- Hfx, Ev. reflexivity.
  - (* EUn *)
    destruct (trans k ns es rho e) as [[[k1 ns1] es1] o1] eqn:E1.
    injection Htr as <- <- <- <-.
    destruct (eval fe prog senv e) as [a1| | |] eqn:Ee1; cbn in Hev; try discriminate Hev.
    destruct (IHe k ns es rho k1 ns1 es1 o1 senv denv prog E1 Hsl Hn He Hc
                  (conj Hfree Hbound) fe a1 Ee1) as [fd1 Hfd1].
    destruct (trans_fresh e k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hkk1 [Hnb1 [Heb1 [Ho1 _]]]].
    exists (S fd1). rewrite eval_dfg_un_step.
    pose proof (eval_dfg_extend fd1 [(k1, DUn u)] [(o1, oport, k1, "0")] ns1 es1 denv k1
                  Heb1 (single_node_fresh k1 (DUn u))
                  ltac:(intros s sp t tp [H|[]]; inversion H; lia)
                  o1 "0" Ho1) as X.
    cbn [app] in X. unfold oport in *.
    match goal with
    | |- rbind ?r _ = _ =>
        assert (R : r = Ok a1) by (etransitivity; [symmetry; exact X | exact Hfd1])
    end.
    rewrite R. exact Hev.
  - (* EBin *)
    apply andb_true_iff in Hsl as [Hsl1 Hsl2].
    destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans k1 ns1 es1 rho e2) as [[[k2 ns2] es2] o2] eqn:E2.
    injection Htr as <- <- <- <-.
    destruct (eval fe prog senv e1) as [a1| | |] eqn:Ee1; cbn in Hev; try discriminate Hev.
    destruct (eval fe prog senv e2) as [a2| | |] eqn:Ee2; cbn in Hev; try discriminate Hev.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hkk1 [Hnb1 [Heb1 [Ho1 [[nx1 [Hns1 Hnx1]] [ex1 [Hes1 Hex1]]]]]]].
    assert (Hc1 : cenv_below rho k1) by (intros x i Hin; apply Hc in Hin; lia).
    destruct (IHe1 k ns es rho k1 ns1 es1 o1 senv denv prog E1 Hsl1 Hn He Hc
                  (conj Hfree Hbound) fe a1 Ee1) as [fd1 Hfd1].
    assert (Hinv1 : env_inv rho senv denv ns1 es1).
    { rewrite Hns1, Hes1.
      apply (env_inv_mono rho senv denv ns es nx1 ex1 k Hc He).
      - intros i nd Hin. apply (proj1 (Hnx1 i nd Hin)).
      - intros s sp t tp Hin. apply (proj1 (Hex1 s sp t tp Hin)).
      - exact (conj Hfree Hbound). }
    destruct (IHe2 k1 ns1 es1 rho k2 ns2 es2 o2 senv denv prog E2 Hsl2 Hnb1 Heb1 Hc1
                  Hinv1 fe a2 Ee2) as [fd2 Hfd2].
    destruct (trans_fresh e2 k1 ns1 es1 rho k2 ns2 es2 o2 E2 Hnb1 Heb1 Hc1)
      as [Hk12 [Hnb2 [Heb2 [Ho2 _]]]].
    set (F := Nat.max fd1 fd2).
    assert (Hex2 : forall s sp t tp,
              In (s, sp, t, tp) [(o1, oport, k2, "0"); (o2, oport, k2, "1")] -> k2 <= t)
      by (intros s sp t tp [H|[H|[]]]; inversion H; lia).
    (* o1 in the big graph *)
    assert (A1 : eval_dfg F {| dnodes := (k2, DBin o) :: ns2;
                               dedges := (o1, oport, k2, "0") :: (o2, oport, k2, "1") :: es2 |}
                          denv o1 "0" = Ok a1).
    { pose proof (eval_dfg_extend F [(k2, DBin o)]
                    [(o1, oport, k2, "0"); (o2, oport, k2, "1")] ns2 es2 denv k2
                    Heb2 (single_node_fresh k2 (DBin o)) Hex2 o1 "0" ltac:(lia)) as X.
      etransitivity; [symmetry; exact X|].
      etransitivity;
        [symmetry; exact (eval_dfg_trans_stable e2 k1 ns1 es1 rho k2 ns2 es2 o2 denv o1 "0" F
                            E2 Hnb1 Heb1 Hc1 Ho1)|].
      exact (eval_dfg_fuel_mono fd1 _ _ _ _ _ Hfd1 F (Nat.le_max_l _ _)). }
    (* o2 in the big graph *)
    assert (A2 : eval_dfg F {| dnodes := (k2, DBin o) :: ns2;
                               dedges := (o1, oport, k2, "0") :: (o2, oport, k2, "1") :: es2 |}
                          denv o2 "0" = Ok a2).
    { pose proof (eval_dfg_extend F [(k2, DBin o)]
                    [(o1, oport, k2, "0"); (o2, oport, k2, "1")] ns2 es2 denv k2
                    Heb2 (single_node_fresh k2 (DBin o)) Hex2 o2 "0" Ho2) as X.
      etransitivity; [symmetry; exact X|].
      exact (eval_dfg_fuel_mono fd2 _ _ _ _ _ Hfd2 F (Nat.le_max_r _ _)). }
    exists (S F). rewrite eval_dfg_bin_step. unfold oport in *.
    match goal with
    | |- rbind ?r1 _ = _ => assert (R1 : r1 = Ok a1) by exact A1
    end.
    rewrite R1. cbn [rbind].
    match goal with
    | |- rbind ?r2 _ = _ => assert (R2 : r2 = Ok a2) by exact A2
    end.
    rewrite R2. exact Hev.
  - (* EIf *)
    discriminate Hsl.
  - (* ELet *)
    apply andb_true_iff in Hsl as [Hsl1 Hsl2].
    destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (eval fe prog senv e1) as [a1| | |] eqn:Ee1; cbn in Hev; try discriminate Hev.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hkk1 [Hnb1 [Heb1 [Ho1 [[nx1 [Hns1 Hnx1]] [ex1 [Hes1 Hex1]]]]]]].
    destruct (IHe1 k ns es rho k1 ns1 es1 o1 senv denv prog E1 Hsl1 Hn He Hc
                  (conj Hfree Hbound) fe a1 Ee1) as [fd1 Hfd1].
    assert (Hinv1 : env_inv rho senv denv ns1 es1).
    { rewrite Hns1, Hes1.
      apply (env_inv_mono rho senv denv ns es nx1 ex1 k Hc He).
      - intros i nd Hin. apply (proj1 (Hnx1 i nd Hin)).
      - intros s sp t tp Hin. apply (proj1 (Hex1 s sp t tp Hin)).
      - exact (conj Hfree Hbound). }
    assert (Hinv2 : env_inv ((x, o1) :: rho) ((x, a1) :: senv) denv ns1 es1)
      by (apply (env_inv_bind rho senv denv ns1 es1 x o1 a1 fd1 Hinv1 Hfd1)).
    assert (Hc2 : cenv_below ((x, o1) :: rho) k1)
      by (intros y j [Hyj|Hin]; [inversion Hyj; subst; exact Ho1 | apply Hc in Hin; lia]).
    destruct (IHe2 k1 ns1 es1 ((x, o1) :: rho) k' ns' es' out ((x, a1) :: senv) denv prog
                  Htr Hsl2 Hnb1 Heb1 Hc2 Hinv2 fe v Hev) as [fd2 Hfd2].
    exists fd2. exact Hfd2.
  - (* EApp *)
    discriminate Hsl.
Qed.

(* TOP-LEVEL COROLLARY: translate e, evaluated with the same environment as
   the source, reproduces the source value. *)
Theorem translate_agree :
  forall e env prog fe v,
    straight_line e = true ->
    eval fe prog env e = Ok v ->
    exists fd, eval_dfg fd (fst (translate e)) env (snd (translate e)) "0" = Ok v.
Proof.
  intros e env prog fe v Hsl Hev.
  unfold translate.
  destruct (trans 0 [] [] [] e) as [[[kf nsf] esf] out] eqn:Etr. cbn [fst snd].
  assert (Hinv : env_inv [] env env [] []).
  { split.
    - intros x _. reflexivity.
    - intros x i Hcl. cbn in Hcl. discriminate. }
  assert (Hn0 : nodes_below [] 0) by (intros i nd Hin; inversion Hin).
  assert (He0 : edges_below [] 0) by (intros s sp t tp Hin; inversion Hin).
  assert (Hc0 : cenv_below [] 0) by (intros x i Hin; inversion Hin).
  destruct (trans_agree e 0 [] [] [] kf nsf esf out env env prog
              Etr Hsl Hn0 He0 Hc0 Hinv fe v Hev) as [fd Hfd].
  exists fd. exact Hfd.
Qed.
