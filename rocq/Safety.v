From Coq Require Import String ZArith List Bool.
Import ListNotations.
From Ribault Require Import Syntax Interp Typing.

Definition value_has_type (v : value) (t : ty) : Prop :=
  match v, t with
  | VInt _,  TInt  => True
  | VBool _, TBool => True
  | _, _           => False
  end.

(* type-stuck (Err) is forbidden; Abort and TimeOut are safe *)
Definition safe (r : result value) (t : ty) : Prop :=
  match r with
  | Ok v    => value_has_type v t
  | Err     => False
  | Abort   => True
  | TimeOut => True
  end.

Definition agree (G : tenv) (env : venv) : Prop :=
  forall x t, tlookup G x = Some t ->
    exists v, vlookup env x = Some v /\ value_has_type v t.

Lemma ty_eqb_eq : forall a b, ty_eqb a b = true -> a = b.
Proof. intros [|] [|]; simpl; congruence. Qed.

Lemma eval_un_safe : forall u t1 t v1,
  ty_un u t1 = Some t -> value_has_type v1 t1 ->
  safe (eval_un u v1) t.
Proof.
  intros u t1 t v1 Hty Hv.
  destruct u, t1; simpl in Hty; try discriminate; inversion Hty; subst;
    destruct v1; simpl in *; tauto.
Qed.

Lemma eval_bin_safe : forall o t1 t2 t v1 v2,
  ty_bin o t1 t2 = Some t ->
  value_has_type v1 t1 -> value_has_type v2 t2 ->
  safe (eval_bin o v1 v2) t.
Proof.
  intros o t1 t2 t v1 v2 Hty H1 H2.
  destruct o, t1, t2; simpl in Hty; try discriminate; inversion Hty; subst;
    destruct v1, v2; simpl in *; try tauto;
    destruct (Z.eqb _ 0); simpl; tauto.
Qed.

Lemma agree_extend : forall G env x t v,
  agree G env -> value_has_type v t ->
  agree ((x,t) :: G) ((x,v) :: env).
Proof.
  intros G env x t v Hag Hv y ty Hy; simpl in *.
  destruct (String.eqb y x).
  - inversion Hy; subst; eauto.
  - apply Hag; exact Hy.
Qed.

Lemma agree_combine : forall params vs ptys,
  Forall2 value_has_type vs ptys ->
  agree (combine params ptys) (combine params vs).
Proof.
  induction params as [|x xs IH]; intros vs ptys Hf.
  - intros y ty Hy; discriminate.
  - destruct Hf as [|v t vs' ts' Hv Hf'].
    + intros y ty Hy; discriminate.
    + apply agree_extend; [apply IH|]; assumption.
Qed.

Lemma flookup_spec : forall p f d,
  flookup p f = Some d -> In d p /\ fd_name d = f.
Proof.
  induction p as [|d0 r IH]; intros f d H; simpl in H; [discriminate|].
  destruct (String.eqb f (fd_name d0)) eqn:E.
  - inversion H; subst. apply String.eqb_eq in E. simpl; auto.
  - destruct (IH _ _ H). simpl; auto.
Qed.

Lemma decl_present_flookup : forall p f,
  decl_present p f = true -> exists d, flookup p f = Some d.
Proof.
  induction p as [|d r IH]; intros f H; simpl in *; [discriminate|].
  destruct (String.eqb f (fd_name d)); simpl in H; eauto.
Qed.

Lemma flookup_sig_covered : forall Sg p f s,
  flookup_sig Sg f = Some s ->
  forallb (fun sp => decl_present p (fst sp)) Sg = true ->
  decl_present p f = true.
Proof.
  induction Sg as [|[g sg] r IH]; intros p f s Hf Hc; simpl in *; [discriminate|].
  apply andb_true_iff in Hc as [Hg Hr].
  destruct (String.eqb f g) eqn:E.
  - apply String.eqb_eq in E; subst; exact Hg.
  - eapply IH; eauto.
Qed.

(* named versions of the inner fixpoints of tc/eval *)
Fixpoint check_args (Sg : fsig) (G : tenv) (es : list expr) (ts : list ty) : bool :=
  match es, ts with
  | [], [] => true
  | e0 :: es', t0 :: ts' =>
      match tc Sg G e0 with
      | Some t => andb (ty_eqb t t0) (check_args Sg G es' ts')
      | None => false
      end
  | _, _ => false
  end.

Fixpoint evargs (fuel : nat) (p : program) (env : venv) (es : list expr)
  : result (list value) :=
  match es with
  | [] => Ok []
  | e0 :: es' =>
      v  <- eval fuel p env e0 ;;
      vs <- evargs fuel p env es' ;;
      Ok (v :: vs)
  end.

Definition safe_args (r : result (list value)) (ts : list ty) : Prop :=
  match r with
  | Ok vs   => Forall2 value_has_type vs ts
  | Err     => False
  | Abort   => True
  | TimeOut => True
  end.

Lemma evargs_safe : forall fuel Sg p G env,
  (forall e t, tc Sg G e = Some t -> safe (eval fuel p env e) t) ->
  forall es ts, check_args Sg G es ts = true ->
  safe_args (evargs fuel p env es) ts.
Proof.
  intros fuel Sg p G env Hev.
  induction es as [|e0 es IH]; intros ts Hc; destruct ts as [|t0 ts];
    simpl in Hc; try discriminate.
  - simpl; constructor.
  - destruct (tc Sg G e0) as [t|] eqn:Ht; [|discriminate].
    apply andb_true_iff in Hc as [Heq Hc]. apply ty_eqb_eq in Heq; subst.
    specialize (Hev _ _ Ht). specialize (IH _ Hc). simpl.
    destruct (eval fuel p env e0); simpl in *; try tauto.
    destruct (evargs fuel p env es); simpl in *; try tauto.
    constructor; assumption.
Qed.

Theorem type_safety : forall fuel Sg p G env e t,
  wt_program Sg p = true ->
  agree G env ->
  tc Sg G e = Some t ->
  safe (eval fuel p env e) t.
Proof.
  induction fuel as [|fuel IH]; intros Sg p G env e t Hwt Hag Htc; [exact I|].
  destruct e as [n|b|x|u e1|o e1 e2|c e1 e2|x e1 e2|f args];
    simpl in Htc |- *.
  - inversion Htc; exact I.
  - inversion Htc; exact I.
  - destruct (Hag _ _ Htc) as [v [Hv Ht]]; rewrite Hv; exact Ht.
  - destruct (tc Sg G e1) as [t1|] eqn:H1; [|discriminate].
    pose proof (IH _ _ _ _ _ _ Hwt Hag H1) as S1.
    destruct (eval fuel p env e1); simpl in *; try tauto.
    eapply eval_un_safe; eauto.
  - destruct (tc Sg G e1) as [t1|] eqn:H1; [|discriminate].
    destruct (tc Sg G e2) as [t2|] eqn:H2; [|discriminate].
    pose proof (IH _ _ _ _ _ _ Hwt Hag H1) as S1.
    pose proof (IH _ _ _ _ _ _ Hwt Hag H2) as S2.
    destruct (eval fuel p env e1); simpl in *; try tauto.
    destruct (eval fuel p env e2); simpl in *; try tauto.
    eapply eval_bin_safe; eauto.
  - destruct (tc Sg G c) as [[|]|] eqn:Hc; try discriminate.
    destruct (tc Sg G e1) as [t1|] eqn:H1; [|discriminate].
    destruct (tc Sg G e2) as [t2|] eqn:H2; [|discriminate].
    destruct (ty_eqb t1 t2) eqn:Heq; [|discriminate].
    apply ty_eqb_eq in Heq; inversion Htc; subst.
    pose proof (IH _ _ _ _ _ _ Hwt Hag Hc) as Sc.
    destruct (eval fuel p env c) as [vc| | |]; simpl in *; try tauto.
    destruct vc as [|[|]]; simpl in Sc; try contradiction; eauto.
  - destruct (tc Sg G e1) as [t1|] eqn:H1; [|discriminate].
    pose proof (IH _ _ _ _ _ _ Hwt Hag H1) as S1.
    destruct (eval fuel p env e1) as [v| | |]; simpl in *; try tauto.
    eapply IH; [exact Hwt| |exact Htc]. apply agree_extend; assumption.
  - destruct (flookup_sig Sg f) as [[ptys rt]|] eqn:Hsig; [|discriminate].
    match type of Htc with
    | context [if ?F args ptys then _ else _] =>
        assert (Heqf : forall l ts, check_args Sg G l ts = F l ts)
          by (induction l as [|a l IHl]; intros [|t0 ts]; simpl; try reflexivity;
              destruct (tc Sg G a); [f_equal; apply IHl|reflexivity]);
        rewrite <- Heqf in Htc;
        destruct (check_args Sg G args ptys) eqn:Hca; [|discriminate]
    end.
    inversion Htc; subst.
    pose proof Hwt as Hwt'.
    apply andb_true_iff in Hwt' as [Hdecls Hcov].
    destruct (decl_present_flookup p f
                (flookup_sig_covered _ _ _ _ Hsig Hcov)) as [d Hfd].
    rewrite Hfd.
    destruct (flookup_spec _ _ _ Hfd) as [Hin Hname].
    pose proof (proj1 (forallb_forall _ _) Hdecls d Hin) as Hwd.
    unfold wt_fundecl in Hwd. rewrite Hname, Hsig in Hwd.
    apply andb_true_iff in Hwd as [Hlen Hbody].
    apply Nat.eqb_eq in Hlen.
    destruct (tc Sg (combine (fd_params d) ptys) (fd_body d)) as [tb|] eqn:Hb;
      [|discriminate].
    apply ty_eqb_eq in Hbody; subst tb.
    pose proof (evargs_safe fuel Sg p G env
                  (fun e t => IH Sg p G env e t Hwt Hag) args ptys Hca) as Sa.
    match goal with
    | |- safe (rbind (?F args) _) _ =>
        assert (Heqe : forall l, evargs fuel p env l = F l)
          by (induction l as [|a l IHl]; simpl; [reflexivity|rewrite IHl; reflexivity]);
        rewrite <- Heqe
    end.
    destruct (evargs fuel p env args) as [vs| | |]; simpl in *; try tauto.
    rewrite Hlen, (Forall2_length Sa), Nat.eqb_refl.
    eapply IH; [exact Hwt| |exact Hb]. apply agree_combine; assumption.
Qed.
