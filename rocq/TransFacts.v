From Coq Require Import String ZArith List Bool Arith Lia.
Import ListNotations.
From Ribault Require Import Syntax Interp Dfg Trans.
Local Open Scope string_scope.

(* every node id in ns is < b *)
Definition nodes_below (ns : list (nodeid * node)) (b : nat) : Prop :=
  forall i nd, In (i, nd) ns -> i < b.

(* every edge source and target in es is < b *)
Definition edges_below (es : list (nodeid * portid * nodeid * portid)) (b : nat) : Prop :=
  forall s sp t tp, In (s, sp, t, tp) es -> s < b /\ t < b.

(* the edge chosen by feeder belongs to the list *)
Lemma feeder_in : forall es tgt tport s sp,
  feeder es tgt tport = Some (s, sp) -> In (s, sp, tgt, tport) es.
Proof.
  induction es as [|[[[s0 sp0] t0] tp0] r IH]; simpl; intros tgt tport s sp H.
  - discriminate.
  - destruct (andb (Nat.eqb t0 tgt) (String.eqb tp0 tport)) eqn:E.
    + apply andb_true_iff in E. destruct E as [E1 E2].
      apply Nat.eqb_eq in E1. apply String.eqb_eq in E2. subst.
      inversion H; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(* a prefix of fresh nodes (id >= b) does not affect the lookup of an id < b *)
Lemma lookup_node_app_skip : forall ns_ex ns m b,
  (forall i nd, In (i, nd) ns_ex -> b <= i) -> m < b ->
  lookup_node (ns_ex ++ ns) m = lookup_node ns m.
Proof.
  induction ns_ex as [|[j nd] r IH]; intros ns m b Hex Hm; simpl.
  - reflexivity.
  - destruct (Nat.eqb m j) eqn:E.
    + apply Nat.eqb_eq in E. subst j.
      specialize (Hex m nd (or_introl eq_refl)). lia.
    + apply (IH ns m b); [| exact Hm].
      intros i nd' Hin. apply (Hex i nd'). right. exact Hin.
Qed.

(* a prefix of edges with a fresh target (>= b) does not affect the feeder of a target < b *)
Lemma feeder_app_skip : forall es_ex es m p b,
  (forall s sp t tp, In (s, sp, t, tp) es_ex -> b <= t) -> m < b ->
  feeder (es_ex ++ es) m p = feeder es m p.
Proof.
  induction es_ex as [|[[[s sp] t] tp] r IH]; intros es m p b Hex Hm; simpl.
  - reflexivity.
  - destruct (andb (Nat.eqb t m) (String.eqb tp p)) eqn:E.
    + apply andb_true_iff in E. destruct E as [E1 _].
      apply Nat.eqb_eq in E1. subst t.
      specialize (Hex s sp m tp (or_introl eq_refl)). lia.
    + apply (IH es m p b); [| exact Hm].
      intros s' sp' t' tp' Hin. apply (Hex s' sp' t' tp'). right. exact Hin.
Qed.

(* MONOTONICITY: evaluating an old node (m < b) is invariant under prepending
   fresh nodes (id >= b) and edges with a fresh target (target >= b). *)
Lemma eval_dfg_extend :
  forall fuel ns_ex es_ex ns es env b,
    edges_below es b ->
    (forall i nd, In (i, nd) ns_ex -> b <= i) ->
    (forall s sp t tp, In (s, sp, t, tp) es_ex -> b <= t) ->
    forall m p, m < b ->
      eval_dfg fuel {| dnodes := ns; dedges := es |} env m p
      = eval_dfg fuel {| dnodes := ns_ex ++ ns; dedges := es_ex ++ es |} env m p.
Proof.
  induction fuel as [|fuel IH]; intros ns_ex es_ex ns es env b Heb Hnx Hex m p Hm.
  - reflexivity.
  - cbn [eval_dfg dnodes dedges]. cbv zeta.
    rewrite (lookup_node_app_skip ns_ex ns m b Hnx Hm).
    assert (Hres : forall p',
      match feeder (es_ex ++ es) m p' with
      | Some (s, sp) =>
          eval_dfg fuel {| dnodes := ns_ex ++ ns; dedges := es_ex ++ es |} env s sp
      | None => Err
      end
      = match feeder es m p' with
        | Some (s, sp) => eval_dfg fuel {| dnodes := ns; dedges := es |} env s sp
        | None => Err
        end).
    { intro p'. rewrite (feeder_app_skip es_ex es m p' b Hex Hm).
      destruct (feeder es m p') as [[s sp]|] eqn:Ef; [| reflexivity].
      assert (Hs : s < b) by (apply (Heb s sp m p'); apply feeder_in; exact Ef).
      symmetry. apply (IH ns_ex es_ex ns es env b Heb Hnx Hex s sp Hs). }
    destruct (lookup_node ns m) as [nd|]; [| reflexivity].
    destruct nd; repeat rewrite Hres; reflexivity.
Qed.

(* every id bound in rho is < b *)
Definition cenv_below (rho : cenv) (b : nat) : Prop :=
  forall x i, In (x, i) rho -> i < b.

(* the variable that clookup resolves belongs to rho *)
Lemma clookup_in : forall rho x i, clookup rho x = Some i -> In (x, i) rho.
Proof.
  induction rho as [|[y j] r IH]; simpl; intros x i H.
  - discriminate.
  - destruct (String.eqb x y) eqn:E.
    + apply String.eqb_eq in E. subst y. inversion H; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(* the freshness postcondition of trans *)
Definition fresh_post (k : nat) (ns : list (nodeid * node))
           (es : list (nodeid * portid * nodeid * portid))
           (k' : nat) (ns' : list (nodeid * node))
           (es' : list (nodeid * portid * nodeid * portid)) (out : nodeid) : Prop :=
    k <= k'
    /\ nodes_below ns' k'
    /\ edges_below es' k'
    /\ out < k'
    /\ (exists ns_ex, ns' = (ns_ex ++ ns)%list
          /\ forall i nd, In (i, nd) ns_ex -> k <= i < k')
    /\ (exists es_ex, es' = (es_ex ++ es)%list
          /\ forall s sp t tp, In (s, sp, t, tp) es_ex -> k <= t < k').

(* one fresh node, no new edge *)
Lemma leaf_fresh : forall k ns es nd,
  nodes_below ns k -> edges_below es k ->
  fresh_post k ns es (S k) ((k, nd) :: ns) es k.
Proof.
  intros k ns es nd Hn He. unfold fresh_post.
  split; [lia|]. split; [|split; [|split; [lia|split]]].
  - intros i nd' [H|H]; [inversion H; lia | apply Hn in H; lia].
  - intros s sp t tp H. apply He in H. lia.
  - exists [(k, nd)]. split; [reflexivity|].
    intros i nd' [H|[]]. inversion H; lia.
  - exists []. split; [reflexivity|]. intros s sp t tp [].
Qed.

(* FRESHNESS: starting from a graph with ids < k, trans produces ids < k',
   with k <= k', the additions in [k,k'), output < k', and the new graph
   is the additions prepended to the old one. Supplies the hypotheses of
   eval_dfg_extend at every compound node of the agreement theorem. *)
Lemma trans_fresh :
  forall e k ns es rho k' ns' es' out,
    trans k ns es rho e = (k', ns', es', out) ->
    nodes_below ns k -> edges_below es k -> cenv_below rho k ->
    k <= k'
    /\ nodes_below ns' k'
    /\ edges_below es' k'
    /\ out < k'
    /\ (exists ns_ex, ns' = (ns_ex ++ ns)%list
          /\ forall i nd, In (i, nd) ns_ex -> k <= i < k')
    /\ (exists es_ex, es' = (es_ex ++ es)%list
          /\ forall s sp t tp, In (s, sp, t, tp) es_ex -> k <= t < k').
Proof.
  intro e.
  change (forall k ns es rho k' ns' es' out,
    trans k ns es rho e = (k', ns', es', out) ->
    nodes_below ns k -> edges_below es k -> cenv_below rho k ->
    fresh_post k ns es k' ns' es' out).
  induction e as [n|b|x|u e1 IH1|o e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3|x e1 IH1 e2 IH2|f args];
    intros k ns es rho k' ns' es' out Htr Hn He Hc; cbn in Htr.
  - inversion Htr; subst. apply leaf_fresh; assumption.
  - inversion Htr; subst. apply leaf_fresh; assumption.
  - destruct (clookup rho x) as [i|] eqn:Ec; inversion Htr; subst.
    + pose proof (Hc _ _ (clookup_in _ _ _ Ec)) as Hi.
      unfold fresh_post. split; [lia|]. split; [exact Hn|].
      split; [exact He|]. split; [exact Hi|]. split.
      * exists []. split; [reflexivity|]. intros i' nd [].
      * exists []. split; [reflexivity|]. intros s sp t tp [].
    + apply leaf_fresh; assumption.
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 [[nx1 [Hns1 Hnx1]] [ex1 [Hes1 Hex1]]]]]]].
    injection Htr as <- <- <- <-. subst ns1 es1. unfold fresh_post.
    split; [lia|]. split; [|split; [|split; [lia|split]]].
    + intros i nd [H|H]; [inversion H; lia | apply Hn1 in H; lia].
    + intros s sp t tp [H|H]; [inversion H; subst; lia | apply He1 in H; lia].
    + exists ((k1, DUn u) :: nx1). split; [reflexivity|].
      intros i nd [H|H]; [inversion H; lia | apply Hnx1 in H; lia].
    + exists ((o1, oport, k1, "0") :: ex1). split; [reflexivity|].
      intros s sp t tp [H|H]; [inversion H; lia | apply Hex1 in H; lia].
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 [[nx1 [Hns1 Hnx1]] [ex1 [Hes1 Hex1]]]]]]].
    assert (Hc1 : cenv_below rho k1) by (intros y j Hy; apply Hc in Hy; lia).
    destruct (trans k1 ns1 es1 rho e2) as [[[k2 ns2] es2] o2] eqn:E2.
    destruct (IH2 _ _ _ _ _ _ _ _ E2 Hn1 He1 Hc1)
      as [Hk2 [Hn2 [He2 [Ho2 [[nx2 [Hns2 Hnx2]] [ex2 [Hes2 Hex2]]]]]]].
    injection Htr as <- <- <- <-. subst ns2 es2 ns1 es1. unfold fresh_post.
    split; [lia|]. split; [|split; [|split; [lia|split]]].
    + intros i nd [H|H]; [inversion H; lia | apply Hn2 in H; lia].
    + intros s sp t tp [H|[H|H]];
        [inversion H; subst; lia | inversion H; subst; lia | apply He2 in H; lia].
    + exists ((k2, DBin o) :: nx2 ++ nx1)%list. split; [rewrite app_assoc; reflexivity|].
      intros i nd [H|H]; [inversion H; lia|].
      apply in_app_iff in H as [H|H]; [apply Hnx2 in H | apply Hnx1 in H]; lia.
    + exists ((o1, oport, k2, "0") :: (o2, oport, k2, "1") :: ex2 ++ ex1)%list.
      split; [rewrite app_assoc; reflexivity|].
      intros s sp t tp [H|[H|H]]; [inversion H; lia | inversion H; lia|].
      apply in_app_iff in H as [H|H]; [apply Hex2 in H | apply Hex1 in H]; lia.
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] oc] eqn:E1.
    destruct (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 [[nx1 [Hns1 Hnx1]] [ex1 [Hes1 Hex1]]]]]]].
    assert (Hc1 : cenv_below rho k1) by (intros y j Hy; apply Hc in Hy; lia).
    destruct (trans k1 ns1 es1 rho e2) as [[[k2 ns2] es2] ot] eqn:E2.
    destruct (IH2 _ _ _ _ _ _ _ _ E2 Hn1 He1 Hc1)
      as [Hk2 [Hn2 [He2 [Ho2 [[nx2 [Hns2 Hnx2]] [ex2 [Hes2 Hex2]]]]]]].
    assert (Hc2 : cenv_below rho k2) by (intros y j Hy; apply Hc in Hy; lia).
    destruct (trans k2 ns2 es2 rho e3) as [[[k3 ns3] es3] of] eqn:E3.
    destruct (IH3 _ _ _ _ _ _ _ _ E3 Hn2 He2 Hc2)
      as [Hk3 [Hn3 [He3 [Ho3 [[nx3 [Hns3 Hnx3]] [ex3 [Hes3 Hex3]]]]]]].
    injection Htr as <- <- <- <-. subst ns3 es3 ns2 es2 ns1 es1. unfold fresh_post.
    split; [lia|]. split; [|split; [|split; [lia|split]]].
    + intros i nd [H|H]; [inversion H; lia | apply Hn3 in H; lia].
    + intros s sp t tp [H|[H|[H|H]]];
        [inversion H; subst; lia | inversion H; subst; lia
        | inversion H; subst; lia | apply He3 in H; lia].
    + exists ((k3, DIf) :: nx3 ++ nx2 ++ nx1)%list.
      split; [rewrite !app_assoc; reflexivity|].
      intros i nd [H|H]; [inversion H; lia|].
      apply in_app_iff in H as [H|H]; [apply Hnx3 in H; lia|].
      apply in_app_iff in H as [H|H]; [apply Hnx2 in H | apply Hnx1 in H]; lia.
    + exists ((oc, oport, k3, "g") :: (ot, oport, k3, "t") :: (of, oport, k3, "f")
              :: ex3 ++ ex2 ++ ex1)%list.
      split; [rewrite !app_assoc; reflexivity|].
      intros s sp t tp [H|[H|[H|H]]]; [inversion H; lia | inversion H; lia | inversion H; lia|].
      apply in_app_iff in H as [H|H]; [apply Hex3 in H; lia|].
      apply in_app_iff in H as [H|H]; [apply Hex2 in H | apply Hex1 in H]; lia.
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 [[nx1 [Hns1 Hnx1]] [ex1 [Hes1 Hex1]]]]]]].
    assert (Hc1 : cenv_below ((x, o1) :: rho) k1)
      by (intros y j [Hy|Hy]; [inversion Hy; subst; lia | apply Hc in Hy; lia]).
    destruct (IH2 _ _ _ _ _ _ _ _ Htr Hn1 He1 Hc1)
      as [Hk2 [Hn2 [He2 [Ho2 [[nx2 [Hns2 Hnx2]] [ex2 [Hes2 Hex2]]]]]]].
    subst. unfold fresh_post.
    split; [lia|]. split; [exact Hn2|]. split; [exact He2|]. split; [exact Ho2|]. split.
    + exists (nx2 ++ nx1)%list. split; [rewrite app_assoc; reflexivity|].
      intros i nd H.
      apply in_app_iff in H as [H|H]; [apply Hnx2 in H | apply Hnx1 in H]; lia.
    + exists (ex2 ++ ex1)%list. split; [rewrite app_assoc; reflexivity|].
      intros s sp t tp H.
      apply in_app_iff in H as [H|H]; [apply Hex2 in H | apply Hex1 in H]; lia.
  - inversion Htr; subst. apply leaf_fresh; assumption.
Qed.

(* FUEL MONOTONICITY: more fuel preserves an Ok result.
   Needed to synchronise the two sub-fuels at a two-input node
   (EBin) in the agreement theorem. *)
Lemma eval_dfg_fuel_mono : forall fd g denv m p v,
  eval_dfg fd g denv m p = Ok v ->
  forall fd', fd <= fd' -> eval_dfg fd' g denv m p = Ok v.
Proof.
  induction fd as [|fd IH]; intros g denv m p v H fd' Hle.
  - cbn in H. discriminate.
  - destruct fd' as [|fd']; [lia|].
    assert (Hle' : fd <= fd') by lia.
    cbn [eval_dfg] in H |- *. cbv zeta in H |- *.
    destruct (lookup_node (dnodes g) m) as [nd|]; [| discriminate H].
    destruct nd; cbn in H |- *; try exact H;
    repeat match type of H with
      | context [match ?A with VInt _ => _ | VBool _ => _ end] =>
          destruct A as [?|[|]]; cbn in H |- *; try discriminate H
      | context [feeder ?E ?M ?P] =>
          let Ef := fresh "Ef" in
          destruct (feeder E M P) as [[? ?]|] eqn:Ef; cbn in H |- *;
          [| discriminate H]
      | context [eval_dfg fd ?G ?D ?S ?SP] =>
          let Es := fresh "Es" in
          destruct (eval_dfg fd G D S SP) eqn:Es; cbn in H; try discriminate H;
          rewrite (IH _ _ _ _ _ Es fd' Hle'); cbn
      end; exact H.
Qed.

(* ENVIRONMENT INVARIANT on the graph (ns,es), relating rho/denv to senv:
   - free variable (clookup None): senv and denv agree on it;
   - let-bound variable (clookup Some i): node i computes the value
     senv holds for it (for some fuel). *)
Definition env_inv (rho : cenv) (senv denv : venv)
                   (ns : list (nodeid * node))
                   (es : list (nodeid * portid * nodeid * portid)) : Prop :=
  (forall x, clookup rho x = None -> vlookup senv x = vlookup denv x)
  /\ (forall x i, clookup rho x = Some i ->
        exists v fd, vlookup senv x = Some v
                  /\ eval_dfg fd {| dnodes := ns; dedges := es |} denv i "0" = Ok v).

(* TRANSPORT: the invariant survives prepending fresh nodes/edges.
   Direct application of eval_dfg_extend at the bound nodes (all < b). *)
Lemma env_inv_mono : forall rho senv denv ns es ns_ex es_ex b,
  cenv_below rho b ->
  edges_below es b ->
  (forall i nd, In (i, nd) ns_ex -> b <= i) ->
  (forall s sp t tp, In (s, sp, t, tp) es_ex -> b <= t) ->
  env_inv rho senv denv ns es ->
  env_inv rho senv denv (ns_ex ++ ns) (es_ex ++ es).
Proof.
  intros rho senv denv ns es ns_ex es_ex b Hc Heb Hnx Hex [Hfree Hbound].
  split.
  - exact Hfree.
  - intros x i Hcl.
    destruct (Hbound x i Hcl) as [v [fd [Hv Hev]]].
    exists v, fd. split; [exact Hv|].
    assert (Hi : i < b).
    { unfold cenv_below in Hc. apply (Hc x i). apply clookup_in. exact Hcl. }
    rewrite <- (eval_dfg_extend fd ns_ex es_ex ns es denv b Heb Hnx Hex i "0" Hi).
    exact Hev.
Qed.
