From Coq Require Import String ZArith List Bool Arith Lia.
Import ListNotations.
From Ribault Require Import Syntax Interp Dfg Trans TransFacts.
Local Open Scope string_scope.

(* no port (target,port) receives two edges: single assignment / no race *)
Definition single_feeder (es : list (nodeid*portid*nodeid*portid)) : Prop :=
  forall s1 sp1 t tp s2 sp2,
    In (s1,sp1,t,tp) es -> In (s2,sp2,t,tp) es -> s1 = s2 /\ sp1 = sp2.

(* every edge goes from a smaller id to a larger one: the id is a topological
   order, so the graph is acyclic *)
Definition edge_ordered (es : list (nodeid*portid*nodeid*portid)) : Prop :=
  forall s sp t tp, In (s,sp,t,tp) es -> s < t.

Lemma trans_edge_ordered :
  forall e k ns es rho k' ns' es' out,
    trans k ns es rho e = (k', ns', es', out) ->
    nodes_below ns k -> edges_below es k -> cenv_below rho k ->
    edge_ordered es -> edge_ordered es'.
Proof.
  induction e as [n|b|x|u e1 IH1|o e1 IH1 e2 IH2|c IHc t IHt f IHf|x e1 IH1 e2 IH2|g args];
    intros k ns es rho k' ns' es' out Htr Hn He Hc Ho; cbn in Htr.
  - injection Htr as <- <- <- <-. exact Ho.
  - injection Htr as <- <- <- <-. exact Ho.
  - destruct (clookup rho x); injection Htr as <- <- <- <-; exact Ho.
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [_ [_ [_ [Ho1 _]]]].
    pose proof (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc Ho) as Hord1.
    injection Htr as <- <- <- <-.
    intros s sp tt tp [H|H]; [inversion H; subst; lia | exact (Hord1 _ _ _ _ H)].
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 _]]]].
    assert (Hc1 : cenv_below rho k1) by (intros y j Hy; apply Hc in Hy; lia).
    pose proof (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc Ho) as Hord1.
    destruct (trans k1 ns1 es1 rho e2) as [[[k2 ns2] es2] o2] eqn:E2.
    destruct (trans_fresh e2 k1 ns1 es1 rho k2 ns2 es2 o2 E2 Hn1 He1 Hc1)
      as [Hk2 [_ [_ [Ho2 _]]]].
    pose proof (IH2 _ _ _ _ _ _ _ _ E2 Hn1 He1 Hc1 Hord1) as Hord2.
    injection Htr as <- <- <- <-.
    intros s sp tt tp [H|[H|H]];
      [inversion H; subst; lia | inversion H; subst; lia | exact (Hord2 _ _ _ _ H)].
  - destruct (trans k ns es rho c) as [[[k1 ns1] es1] oc] eqn:E1.
    destruct (trans_fresh c k ns es rho k1 ns1 es1 oc E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Hoc _]]]].
    assert (Hc1 : cenv_below rho k1) by (intros y j Hy; apply Hc in Hy; lia).
    pose proof (IHc _ _ _ _ _ _ _ _ E1 Hn He Hc Ho) as Hord1.
    destruct (trans k1 ns1 es1 rho t) as [[[k2 ns2] es2] ot] eqn:E2.
    destruct (trans_fresh t k1 ns1 es1 rho k2 ns2 es2 ot E2 Hn1 He1 Hc1)
      as [Hk2 [Hn2 [He2 [Hot _]]]].
    assert (Hc2 : cenv_below rho k2) by (intros y j Hy; apply Hc in Hy; lia).
    pose proof (IHt _ _ _ _ _ _ _ _ E2 Hn1 He1 Hc1 Hord1) as Hord2.
    destruct (trans k2 ns2 es2 rho f) as [[[k3 ns3] es3] of] eqn:E3.
    destruct (trans_fresh f k2 ns2 es2 rho k3 ns3 es3 of E3 Hn2 He2 Hc2)
      as [Hk3 [_ [_ [Hof _]]]].
    pose proof (IHf _ _ _ _ _ _ _ _ E3 Hn2 He2 Hc2 Hord2) as Hord3.
    injection Htr as <- <- <- <-.
    intros s sp tt tp [H|[H|[H|H]]];
      [inversion H; subst; lia | inversion H; subst; lia | inversion H; subst; lia
      | exact (Hord3 _ _ _ _ H)].
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 _]]]].
    assert (Hc2 : cenv_below ((x, o1) :: rho) k1)
      by (intros y j [Hy|Hy]; [inversion Hy; subst; lia | apply Hc in Hy; lia]).
    pose proof (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc Ho) as Hord1.
    exact (IH2 _ _ _ _ _ _ _ _ Htr Hn1 He1 Hc2 Hord1).
  - injection Htr as <- <- <- <-. exact Ho.
Qed.

Lemma trans_single_feeder :
  forall e k ns es rho k' ns' es' out,
    trans k ns es rho e = (k', ns', es', out) ->
    nodes_below ns k -> edges_below es k -> cenv_below rho k ->
    single_feeder es -> single_feeder es'.
Proof.
  induction e as [n|b|x|u e1 IH1|o e1 IH1 e2 IH2|c IHc t IHt f IHf|x e1 IH1 e2 IH2|g args];
    intros k ns es rho k' ns' es' out Htr Hn He Hc Hsf; cbn in Htr.
  - injection Htr as <- <- <- <-. exact Hsf.
  - injection Htr as <- <- <- <-. exact Hsf.
  - destruct (clookup rho x); injection Htr as <- <- <- <-; exact Hsf.
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [_ [_ [He1 _]]].
    pose proof (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc Hsf) as Hsf1.
    injection Htr as <- <- <- <-.
    intros s1 sp1 tt tp s2 sp2 H1 H2.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2];
      first [ solve [inversion H1; inversion H2; subst; split; reflexivity]
            | solve [inversion H1; subst; pose proof (He1 _ _ _ _ H2); lia]
            | solve [inversion H2; subst; pose proof (He1 _ _ _ _ H1); lia]
            | exact (Hsf1 _ _ _ _ _ _ H1 H2) ].
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 _]]]].
    assert (Hc1 : cenv_below rho k1) by (intros y j Hy; apply Hc in Hy; lia).
    pose proof (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc Hsf) as Hsf1.
    destruct (trans k1 ns1 es1 rho e2) as [[[k2 ns2] es2] o2] eqn:E2.
    destruct (trans_fresh e2 k1 ns1 es1 rho k2 ns2 es2 o2 E2 Hn1 He1 Hc1)
      as [_ [_ [He2 _]]].
    pose proof (IH2 _ _ _ _ _ _ _ _ E2 Hn1 He1 Hc1 Hsf1) as Hsf2.
    injection Htr as <- <- <- <-.
    intros s1 sp1 tt tp s2 sp2 H1 H2.
    destruct H1 as [H1|[H1|H1]]; destruct H2 as [H2|[H2|H2]];
      first [ solve [inversion H1; inversion H2; subst; split; reflexivity]
            | solve [inversion H1; subst; inversion H2]
            | solve [inversion H1; subst; pose proof (He2 _ _ _ _ H2); lia]
            | solve [inversion H2; subst; pose proof (He2 _ _ _ _ H1); lia]
            | exact (Hsf2 _ _ _ _ _ _ H1 H2) ].
  - destruct (trans k ns es rho c) as [[[k1 ns1] es1] oc] eqn:E1.
    destruct (trans_fresh c k ns es rho k1 ns1 es1 oc E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Hoc _]]]].
    assert (Hc1 : cenv_below rho k1) by (intros y j Hy; apply Hc in Hy; lia).
    pose proof (IHc _ _ _ _ _ _ _ _ E1 Hn He Hc Hsf) as Hsf1.
    destruct (trans k1 ns1 es1 rho t) as [[[k2 ns2] es2] ot] eqn:E2.
    destruct (trans_fresh t k1 ns1 es1 rho k2 ns2 es2 ot E2 Hn1 He1 Hc1)
      as [Hk2 [Hn2 [He2 [Hot _]]]].
    assert (Hc2 : cenv_below rho k2) by (intros y j Hy; apply Hc in Hy; lia).
    pose proof (IHt _ _ _ _ _ _ _ _ E2 Hn1 He1 Hc1 Hsf1) as Hsf2.
    destruct (trans k2 ns2 es2 rho f) as [[[k3 ns3] es3] of] eqn:E3.
    destruct (trans_fresh f k2 ns2 es2 rho k3 ns3 es3 of E3 Hn2 He2 Hc2)
      as [_ [_ [He3 _]]].
    pose proof (IHf _ _ _ _ _ _ _ _ E3 Hn2 He2 Hc2 Hsf2) as Hsf3.
    injection Htr as <- <- <- <-.
    intros s1 sp1 tt tp s2 sp2 H1 H2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|H2]]];
      first [ solve [inversion H1; inversion H2; subst; split; reflexivity]
            | solve [inversion H1; subst; inversion H2]
            | solve [inversion H1; subst; pose proof (He3 _ _ _ _ H2); lia]
            | solve [inversion H2; subst; pose proof (He3 _ _ _ _ H1); lia]
            | exact (Hsf3 _ _ _ _ _ _ H1 H2) ].
  - destruct (trans k ns es rho e1) as [[[k1 ns1] es1] o1] eqn:E1.
    destruct (trans_fresh e1 k ns es rho k1 ns1 es1 o1 E1 Hn He Hc)
      as [Hk1 [Hn1 [He1 [Ho1 _]]]].
    assert (Hc2 : cenv_below ((x, o1) :: rho) k1)
      by (intros y j [Hy|Hy]; [inversion Hy; subst; lia | apply Hc in Hy; lia]).
    pose proof (IH1 _ _ _ _ _ _ _ _ E1 Hn He Hc Hsf) as Hsf1.
    exact (IH2 _ _ _ _ _ _ _ _ Htr Hn1 He1 Hc2 Hsf1).
  - injection Htr as <- <- <- <-. exact Hsf.
Qed.

Theorem translate_edge_ordered : forall e,
  edge_ordered (dedges (fst (translate e))).
Proof.
  intro e. unfold translate.
  destruct (trans 0 [] [] [] e) as [[[kf nsf] esf] out] eqn:Etr. cbn [fst dedges].
  apply (trans_edge_ordered e 0 [] [] [] kf nsf esf out Etr).
  - intros i nd [].
  - intros s sp t tp [].
  - intros x i [].
  - intros s sp t tp [].
Qed.

Theorem translate_single_feeder : forall e,
  single_feeder (dedges (fst (translate e))).
Proof.
  intro e. unfold translate.
  destruct (trans 0 [] [] [] e) as [[[kf nsf] esf] out] eqn:Etr. cbn [fst dedges].
  apply (trans_single_feeder e 0 [] [] [] kf nsf esf out Etr).
  - intros i nd [].
  - intros s sp t tp [].
  - intros x i [].
  - intros s1 sp1 t tp s2 sp2 [].   (* single_feeder [] vacuous *)
Qed.
