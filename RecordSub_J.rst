RecordSub\_J: レコードのサブタイプ
==================================

中核部の定義
------------

構文
^^^^

::

    Inductive ty : Type :=

Well-Formedness
^^^^^^^^^^^^^^^

::

    Inductive record_ty : ty -> Prop :=
      | rty_nil :
            record_ty ty_rnil
      | rty_cons : forall i T1 T2,
            record_ty (ty_rcons i T1 T2).

    Inductive record_tm : tm -> Prop :=
      | rtm_nil :
            record_tm tm_rnil
      | rtm_cons : forall i t1 t2,
            record_tm (tm_rcons i t1 t2).

    Inductive well_formed_ty : ty -> Prop :=
      | wfty_Top :
            well_formed_ty ty_Top
      | wfty_base : forall i,
            well_formed_ty (ty_base i)
      | wfty_arrow : forall T1 T2,
            well_formed_ty T1 ->
            well_formed_ty T2 ->
            well_formed_ty (ty_arrow T1 T2)
      | wfty_rnil :
            well_formed_ty ty_rnil
      | wfty_rcons : forall i T1 T2,
            well_formed_ty T1 ->
            well_formed_ty T2 ->
            record_ty T2 ->
            well_formed_ty (ty_rcons i T1 T2).

    Hint Constructors record_ty record_tm well_formed_ty.

置換
^^^^

::

    Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
      match t with
      | tm_var y => if beq_id x y then s else t
      | tm_abs y T t1 =>  tm_abs y T (if beq_id x y then t1 else (subst x s t1))
      | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
      | tm_proj t1 i => tm_proj (subst x s t1) i
      | tm_rnil => tm_rnil
      | tm_rcons i t1 tr2 => tm_rcons i (subst x s t1) (subst x s tr2)
      end.

簡約
^^^^

::

    Inductive value : tm -> Prop :=
      | v_abs : forall x T t,
          value (tm_abs x T t)
      | v_rnil : value tm_rnil
      | v_rcons : forall i v vr,
          value v ->
          value vr ->
          value (tm_rcons i v vr).

    Hint Constructors value.

    Fixpoint ty_lookup (i:id) (Tr:ty) : option ty :=
      match Tr with
      | ty_rcons i' T Tr' => if beq_id i i' then Some T else ty_lookup i Tr'
      | _ => None
      end.

    Fixpoint tm_lookup (i:id) (tr:tm) : option tm :=
      match tr with
      | tm_rcons i' t tr' => if beq_id i i' then Some t else tm_lookup i tr'
      | _ => None
      end.

    Reserved Notation "t1 '==>' t2" (at level 40).

    Inductive step : tm -> tm -> Prop :=
      | ST_AppAbs : forall x T t12 v2,
             value v2 ->
             (tm_app (tm_abs x T t12) v2) ==> (subst x v2 t12)
      | ST_App1 : forall t1 t1' t2,
             t1 ==> t1' ->
             (tm_app t1 t2) ==> (tm_app t1' t2)
      | ST_App2 : forall v1 t2 t2',
             value v1 ->
             t2 ==> t2' ->
             (tm_app v1 t2) ==> (tm_app v1  t2')
      | ST_Proj1 : forall tr tr' i,
            tr ==> tr' ->
            (tm_proj tr i) ==> (tm_proj tr' i)
      | ST_ProjRcd : forall tr i vi,
            value tr ->
            tm_lookup i tr = Some vi    ->
           (tm_proj tr i) ==> vi
      | ST_Rcd_Head : forall i t1 t1' tr2,
            t1 ==> t1' ->
            (tm_rcons i t1 tr2) ==> (tm_rcons i t1' tr2)
      | ST_Rcd_Tail : forall i v1 tr2 tr2',
            value v1 ->
            tr2 ==> tr2' ->
            (tm_rcons i v1 tr2) ==> (tm_rcons i v1 tr2')

    where "t1 '==>' t2" := (step t1 t2).

    Tactic Notation "step_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
      | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd" | Case_aux c "ST_Rcd"
      | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail" ].

    Hint Constructors step.

サブタイプ
----------

おもしろい部分に来ました。サブタイプ関係を定義し、その重要な技術的性質のいくつかを調べることから始めます。

定義
~~~~

サブタイプの定義は、本質的には、動機付けの議論で概観した通りです。ただ、いくつかの規則に付加条件として
well-formedness を追加する必要があります。

::

    Inductive subtype : ty -> ty -> Prop :=

サブタイプの例と練習問題
~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module Examples.

    Notation x := (Id 0).
    Notation y := (Id 1).
    Notation z := (Id 2).
    Notation j := (Id 3).
    Notation k := (Id 4).
    Notation i := (Id 5).
    Notation A := (ty_base (Id 6)).
    Notation B := (ty_base (Id 7)).
    Notation C := (ty_base (Id 8)).

    Definition ty_rcd_j  :=
      (ty_rcons j (ty_arrow B B) ty_rnil).

以下の事実のほとんどはCoqで証明することは簡単です。練習問題の効果を最大にするため、どのように証明するかを理解していることを紙の上でも確認しなさい!

練習問題: ★★
''''''''''''

::

    Example subtyping_example_1 :
      subtype ty_rcd_kj ty_rcd_j.
     Admitted.

☐

練習問題: ★
'''''''''''

::

    Example subtyping_example_2 :
      subtype (ty_arrow ty_Top ty_rcd_kj)
              (ty_arrow (ty_arrow C C) ty_rcd_j).
     Admitted.

☐

練習問題: ★
'''''''''''

::

    Example subtyping_example_3 :
      subtype (ty_arrow ty_rnil (ty_rcons j A ty_rnil))
              (ty_arrow (ty_rcons k B ty_rnil) ty_rnil).
     Admitted.

☐

練習問題: ★★
''''''''''''

::

    Example subtyping_example_4 :
      subtype (ty_rcons x A (ty_rcons y B (ty_rcons z C ty_rnil)))
              (ty_rcons z C (ty_rcons y B (ty_rcons x A ty_rnil))).
     Admitted.

☐

::

    Definition tm_rcd_kj :=
      (tm_rcons k (tm_abs z A (tm_var z))
               (tm_rcons j (tm_abs z B (tm_var z))
                          tm_rnil)).

    End Examples.

サブタイプの性質
~~~~~~~~~~~~~~~~

Well-Formedness
^^^^^^^^^^^^^^^

::

    Lemma subtype__wf : forall S T,
      subtype S T ->
      well_formed_ty T /\ well_formed_ty S.
    Proof with eauto.
      intros S T Hsub.
      subtype_cases (induction Hsub) Case;
        intros; try (destruct IHHsub1; destruct IHHsub2)...
      Case "S_RcdPerm".
        split... inversion H. subst. inversion H5...  Qed.

    Lemma wf_rcd_lookup : forall i T Ti,
      well_formed_ty T ->
      ty_lookup i T = Some Ti ->
      well_formed_ty Ti.
    Proof with eauto.
      intros i T.
      ty_cases (induction T) Case; intros; try solve by inversion.
      Case "ty_rcons".
        inversion H. subst. unfold ty_lookup in H0.
        remember (beq_id i i0) as b. destruct b; subst...
        inversion H0. subst...  Qed.

フィールド参照
^^^^^^^^^^^^^^

サブタイプがあることで、レコードマッチング補題はいくらか複雑になります。それには2つの理由があります。1つはレコード型が対応する項の正確な構造を記述する必要がなくなることです。2つ目は、\ ``has_type``\ の導出に関する帰納法を使う推論が一般には難しくなることです。なぜなら、\ ``has_type``\ が構文指向ではなくなるからです。

::

    Lemma rcd_types_match : forall S T i Ti,
      subtype S T ->
      ty_lookup i T = Some Ti ->
      exists Si, ty_lookup i S = Some Si /\ subtype Si Ti.
    Proof with (eauto using wf_rcd_lookup).
      intros S T i Ti Hsub Hget. generalize dependent Ti.
      subtype_cases (induction Hsub) Case; intros Ti Hget;
        try solve by inversion.
      Case "S_Refl".
        exists Ti...
      Case "S_Trans".
        destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
        destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
        exists Si...
      Case "S_RcdDepth".
        rename i0 into k.
        unfold ty_lookup. unfold ty_lookup in Hget.
        remember (beq_id i k) as b. destruct b...
        SCase "i = k -- we're looking up the first field".
          inversion Hget. subst. exists S1...
      Case "S_RcdPerm".
        exists Ti. split.
        SCase "lookup".
          unfold ty_lookup. unfold ty_lookup in Hget.
          remember (beq_id i i1) as b. destruct b...
          SSCase "i = i1 -- we're looking up the first field".
            remember (beq_id i i2) as b. destruct b...
            SSSCase "i = i2 - -contradictory".
              destruct H0.
              apply beq_id_eq in Heqb. apply beq_id_eq in Heqb0.
              subst...
        SCase "subtype".
          inversion H. subst. inversion H5. subst...  Qed.

練習問題: ★★★ (rcd\_types\_match\_informal)
'''''''''''''''''''''''''''''''''''''''''''

``rcd_types_match``\ 補題の非形式的証明を注意深く記述しなさい。

☐

反転補題
^^^^^^^^

練習問題: ★★★, optional (sub\_inversion\_arrow)
'''''''''''''''''''''''''''''''''''''''''''''''

::

    Lemma sub_inversion_arrow : forall U V1 V2,
         subtype U (ty_arrow V1 V2) ->
         exists U1, exists U2,
           (U=(ty_arrow U1 U2)) /\ (subtype V1 U1) /\ (subtype U2 V2).
    Proof with eauto.
      intros U V1 V2 Hs.
      remember (ty_arrow V1 V2) as V.
      generalize dependent V2. generalize dependent V1.

型付け
------

::

    Definition context := id -> (option ty).
    Definition empty : context := (fun _ => None).
    Definition extend (Gamma : context) (x:id) (T : ty) :=
      fun x' => if beq_id x x' then Some T else Gamma x'.

    Inductive has_type : context -> tm -> ty -> Prop :=
      | T_Var : forall Gamma x T,
          Gamma x = Some T ->
          well_formed_ty T ->
          has_type Gamma (tm_var x) T
      | T_Abs : forall Gamma x T11 T12 t12,
          well_formed_ty T11 ->
          has_type (extend Gamma x T11) t12 T12 ->
          has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
      | T_App : forall T1 T2 Gamma t1 t2,
          has_type Gamma t1 (ty_arrow T1 T2) ->
          has_type Gamma t2 T1 ->
          has_type Gamma (tm_app t1 t2) T2
      | T_Proj : forall Gamma i t T Ti,
          has_type Gamma t T ->
          ty_lookup i T = Some Ti ->
          has_type Gamma (tm_proj t i) Ti

型付けの例
~~~~~~~~~~

::

    Module Examples2.
    Import Examples.

練習問題: ★
'''''''''''

::

    Example typing_example_0 :
      has_type empty
               (tm_rcons k (tm_abs z A (tm_var z))
                         (tm_rcons j (tm_abs z B (tm_var z))
                                   tm_rnil))
               ty_rcd_kj.
     Admitted.

☐

練習問題: ★★
''''''''''''

::

    Example typing_example_1 :
      has_type empty
               (tm_app (tm_abs x ty_rcd_j (tm_proj (tm_var x) j))
                       (tm_rcd_kj))
               (ty_arrow B B).
     Admitted.

☐

練習問題: ★★, optional
''''''''''''''''''''''

::

    Example typing_example_2 :
      has_type empty
               (tm_app (tm_abs z (ty_arrow (ty_arrow C C) ty_rcd_j)
                               (tm_proj (tm_app (tm_var z)
                                                (tm_abs x C (tm_var x)))
                                        j))
                       (tm_abs z (ty_arrow C C) tm_rcd_kj))
               (ty_arrow B B).
     Admitted.

☐

::

    End Examples2.

型付けの性質
~~~~~~~~~~~~

Well-Formedness
^^^^^^^^^^^^^^^

::

    Lemma has_type__wf : forall Gamma t T,
      has_type Gamma t T -> well_formed_ty T.
    Proof with eauto.
      intros Gamma t T Htyp.
      has_type_cases (induction Htyp) Case...
      Case "T_App".
        inversion IHHtyp1...
      Case "T_Proj".
        eapply wf_rcd_lookup...
      Case "T_Sub".
        apply subtype__wf in H.
        destruct H...
    Qed.

    Lemma step_preserves_record_tm : forall tr tr',
      record_tm tr ->
      tr ==> tr' ->
      record_tm tr'.
    Proof.
      intros tr tr' Hrt Hstp.
      inversion Hrt; subst; inversion Hstp; subst; eauto.
    Qed.

フィールド参照
^^^^^^^^^^^^^^

::

    Lemma lookup_field_in_value : forall v T i Ti,
      value v ->
      has_type empty v T ->
      ty_lookup i T = Some Ti ->
      exists vi, tm_lookup i v = Some vi /\ has_type empty vi Ti.
    Proof with eauto.
      remember empty as Gamma.
      intros t T i Ti Hval Htyp. revert Ti HeqGamma Hval.
      has_type_cases (induction Htyp) Case; intros; subst; try solve by inversion.
      Case "T_Sub".
        apply (rcd_types_match S) in H0... destruct H0 as [Si [HgetSi Hsub]].
        destruct (IHHtyp Si) as [vi [Hget Htyvi]]...
      Case "T_RCons".
        simpl in H0. simpl. simpl in H1.
        remember (beq_id i i0) as b. destruct b.
        SCase "i is first".
          inversion H1. subst. exists t...
        SCase "i in tail".
          destruct (IHHtyp2 Ti) as [vi [get Htyvi]]...
          inversion Hval...  Qed.

進行
^^^^

練習問題: ★★★ (canonical\_forms\_of\_arrow\_types)
''''''''''''''''''''''''''''''''''''''''''''''''''

::

    Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
         has_type Gamma s (ty_arrow T1 T2) ->
         value s ->
         exists x, exists S1, exists s2,
            s = tm_abs x S1 s2.
    Proof with eauto.
       Admitted.

☐

::

    Theorem progress : forall t T,
         has_type empty t T ->
         value t \/ exists t', t ==> t'.
    Proof with eauto.
      intros t T Ht.
      remember empty as Gamma.
      revert HeqGamma.
      has_type_cases (induction Ht) Case;
        intros HeqGamma; subst...
      Case "T_Var".
        inversion H.
      Case "T_App".
        right.
        destruct IHHt1; subst...
        SCase "t1 is a value".
          destruct IHHt2; subst...
          SSCase "t2 is a value".
            destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
              as [x [S1 [t12 Heqt1]]]...
            subst. exists (subst x t2 t12)...
          SSCase "t2 steps".
            destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
        SCase "t1 steps".
          destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
      Case "T_Proj".
        right. destruct IHHt...
        SCase "rcd is value".
          destruct (lookup_field_in_value t T i Ti) as [t' [Hget Ht']]...
        SCase "rcd_steps".
          destruct H0 as [t' Hstp]. exists (tm_proj t' i)...
      Case "T_RCons".
        destruct IHHt1...
        SCase "head is a value".
          destruct IHHt2...
          SSCase "tail steps".
            right. destruct H2 as [tr' Hstp].
            exists (tm_rcons i t tr')...
        SCase "head steps".
          right. destruct H1 as [t' Hstp].
          exists (tm_rcons i t' tr)...  Qed.

進行の非形式的証明:

定理：
任意の項\ ``t``\ と型\ ``T``\ について、\ ``empty |- t : T``\ ならば、\ ``t``\ は値であるか、ある項\ ``t'``\ について\ ``t ==> t'``\ である。

証明
:``t``\ と\ ``T``\ が\ ``empty |- t : T``\ を満たすとする。型付け導出についての帰納法を使う。\ ``T_Abs``\ と\ ``T_RNil``\ の場合は自明である。それは、関数抽象と\ ``{}``\ は常に値だからである。\ ``T_Var``\ の場合は考えなくて良い。なぜなら変数は空コンテキストで型付けできないからである。

-  型付け導出の最後のステップが\ ``T_App``\ の適用だった場合、
   項\ ``t1``t2``\ と型\ ``T1``T2``\ があって\ ``t = t1 t2``\ 、\ ``T = T2``\ 、\ ``empty |- t1 : T1 -> T2``\ 、\ ``empty |- t2 : T1``\ となる。
   これらの型付け導出の帰納法の仮定より、\ ``t1``\ は値であるかステップを進めることができ、また\ ``t2``\ は値であるかステップを進めることができる。それぞれの場合を考える:

   -  ある項\ ``t1'``\ について\ ``t1 ==> t1'``\ とする。
      すると\ ``ST_App1``\ より\ ``t1 t2 ==> t1' t2``\ である。

   -  そうでないならば\ ``t1``\ は値である。

   -  ある項\ ``t2'``\ について\ ``t2 ==> t2'``\ とする。
      すると\ ``t1``\ が値であることから規則\ ``ST_App2``\ により\ ``t1 t2 ==> t1 t2'``\ となる。
   -  そうでなければ\ ``t2``\ は値である。補題\ ``canonical_forms_for_arrow_types``\ により、
      ある\ ``x``\ 、\ ``S1``\ 、\ ``s2``\ について\ ``t1 = \x:S1.s2``\ である。すると\ ``t2``\ が値であることから、\ ``ST_AppAbs``\ により\ ``(\x:S1.s2) t2 ==> [t2/x``\ s2]
      となる。

-  導出の最後のステップが\ ``T_Proj``\ の適用だった場合、
   項\ ``tr``\ 、型\ ``Tr``\ 、ラベル\ ``i``\ が存在して\ ``t = tr.i``\ 、\ ``empty |- tr : Tr``\ 、\ ``ty_lookup i Tr = Some T``\ となる。
   導出の一部である型付け導出の帰納仮定より、\ ``tr``\ は値であるかステップを進むことができる。もしある項\ ``tr'``\ について\ ``tr ==> tr'``\ ならば、規則\ ``ST_Proj1``\ より\ ``tr.i ==> tr'.i``\ となる。
   そうでなければ、\ ``tr``\ は値である。この場合、補題\ ``lookup_field_in_value``\ により項\ ``ti``\ が存在して\ ``tm_lookup i tr = Some ti``\ となる。これから、規則\ ``ST_ProjRcd``\ より\ ``tr.i ==> ti``\ となる。

-  導出の最後のステップが\ ``T_Sub``\ の適用だった場合、
   型\ ``S``\ が存在して\ ``S <: T``\ かつ\ ``empty |- t : S``\ となる。導出の一部である型付け導出の帰納法の仮定から求める結果がすぐに得られる。

-  導出の最後のステップが\ ``T_RCons``\ の適用だった場合、
   項\ ``t1``tr``\ 、型\ ``T1 Tr``\ 、ラベル\ ``i``\ が存在して\ ``t = {i=t1, tr}``\ 、\ ``T = {i:T1, Tr}``\ 、\ ``record_tm tr``\ 、\ ``record_tm Tr``\ 、\ ``empty |- t1 : T1``\ 、\ ``empty |- tr : Tr``\ となる。
   これらの型付け導出についての帰納法の仮定より、\ ``t1``\ は値であるか、ステップを進めることができ、\ ``tr``\ は値であるかステップを進めることができることが言える。それそれの場合を考える:

   -  ある項\ ``t1'``\ について\ ``t1 ==> t1'``\ とする。
      すると規則\ ``ST_Rcd_Head``\ から\ ``{i=t1, tr} ==> {i=t1', tr}``\ となる。

   -  そうではないとき、\ ``t1``\ は値である。

   -  ある項\ ``tr'``\ について\ ``tr ==> tr'``\ とする。
      すると\ ``t1``\ が値であることから、規則\ ``ST_Rcd_Tail``\ より\ ``{i=t1, tr} ==> {i=t1, tr'}``\ となる。
   -  そうではないとき、\ ``tr``\ も値である。すると、\ ``v_rcons``\ から\ ``{i=t1, tr}``\ は値である。

反転補題
^^^^^^^^

::

    Lemma typing_inversion_var : forall Gamma x T,
      has_type Gamma (tm_var x) T ->
      exists S,
        Gamma x = Some S /\ subtype S T.
    Proof with eauto.
      intros Gamma x T Hty.
      remember (tm_var x) as t.
      has_type_cases (induction Hty) Case; intros;
        inversion Heqt; subst; try solve by inversion.
      Case "T_Var".
        exists T...
      Case "T_Sub".
        destruct IHHty as [U [Hctx HsubU]]... Qed.

    Lemma typing_inversion_app : forall Gamma t1 t2 T2,
      has_type Gamma (tm_app t1 t2) T2 ->
      exists T1,
        has_type Gamma t1 (ty_arrow T1 T2) /\
        has_type Gamma t2 T1.
    Proof with eauto.
      intros Gamma t1 t2 T2 Hty.
      remember (tm_app t1 t2) as t.
      has_type_cases (induction Hty) Case; intros;
        inversion Heqt; subst; try solve by inversion.
      Case "T_App".
        exists T1...
      Case "T_Sub".
        destruct IHHty as [U1 [Hty1 Hty2]]...
        assert (Hwf := has_type__wf _ _ _ Hty2).
        exists U1...  Qed.

    Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
         has_type Gamma (tm_abs x S1 t2) T ->
         (exists S2, subtype (ty_arrow S1 S2) T
                  /\ has_type (extend Gamma x S1) t2 S2).
    Proof with eauto.
      intros Gamma x S1 t2 T H.
      remember (tm_abs x S1 t2) as t.
      has_type_cases (induction H) Case;
        inversion Heqt; subst; intros; try solve by inversion.
      Case "T_Abs".
        assert (Hwf := has_type__wf _ _ _ H0).
        exists T12...
      Case "T_Sub".
        destruct IHhas_type as [S2 [Hsub Hty]]...
        Qed.

    Lemma typing_inversion_proj : forall Gamma i t1 Ti,
      has_type Gamma (tm_proj t1 i) Ti ->
      exists T, exists Si,
        ty_lookup i T = Some Si /\ subtype Si Ti /\ has_type Gamma t1 T.
    Proof with eauto.
      intros Gamma i t1 Ti H.
      remember (tm_proj t1 i) as t.
      has_type_cases (induction H) Case;
        inversion Heqt; subst; intros; try solve by inversion.
      Case "T_Proj".
        assert (well_formed_ty Ti) as Hwf.
          SCase "pf of assertion".
            apply (wf_rcd_lookup i T Ti)...
            apply has_type__wf in H...
        exists T. exists Ti...
      Case "T_Sub".
        destruct IHhas_type as [U [Ui [Hget [Hsub Hty]]]]...
        exists U. exists Ui...  Qed.

    Lemma typing_inversion_rcons : forall Gamma i ti tr T,
      has_type Gamma (tm_rcons i ti tr) T ->
      exists Si, exists Sr,
        subtype (ty_rcons i Si Sr) T /\ has_type Gamma ti Si /\
        record_tm tr /\ has_type Gamma tr Sr.
    Proof with eauto.
      intros Gamma i ti tr T Hty.
      remember (tm_rcons i ti tr) as t.
      has_type_cases (induction Hty) Case;
        inversion Heqt; subst...
      Case "T_Sub".
        apply IHHty in H0.
        destruct H0 as [Ri [Rr [HsubRS [HtypRi HtypRr]]]].
        exists Ri. exists Rr...
      Case "T_RCons".
        assert (well_formed_ty (ty_rcons i T Tr)) as Hwf.
          SCase "pf of assertion".
            apply has_type__wf in Hty1.
            apply has_type__wf in Hty2...
        exists T. exists Tr...  Qed.

    Lemma abs_arrow : forall x S1 s2 T1 T2,
      has_type empty (tm_abs x S1 s2) (ty_arrow T1 T2) ->
         subtype T1 S1
      /\ has_type (extend empty x S1) s2 T2.
    Proof with eauto.
      intros x S1 s2 T1 T2 Hty.
      apply typing_inversion_abs in Hty.
      destruct Hty as [S2 [Hsub Hty]].
      apply sub_inversion_arrow in Hsub.
      destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
      inversion Heq; subst...  Qed.

コンテキスト不変性
^^^^^^^^^^^^^^^^^^

::

    Inductive appears_free_in : id -> tm -> Prop :=
      | afi_var : forall x,
          appears_free_in x (tm_var x)
      | afi_app1 : forall x t1 t2,
          appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
      | afi_app2 : forall x t1 t2,
          appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
      | afi_abs : forall x y T11 t12,
            y <> x  ->
            appears_free_in x t12 ->
            appears_free_in x (tm_abs y T11 t12)
      | afi_proj : forall x t i,
          appears_free_in x t ->
          appears_free_in x (tm_proj t i)
      | afi_rhead : forall x i t tr,
          appears_free_in x t ->
          appears_free_in x (tm_rcons i t tr)
      | afi_rtail : forall x i t tr,
          appears_free_in x tr ->
          appears_free_in x (tm_rcons i t tr).

    Hint Constructors appears_free_in.

    Lemma context_invariance : forall Gamma Gamma' t S,
         has_type Gamma t S  ->
         (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
         has_type Gamma' t S.
    Proof with eauto.
      intros. generalize dependent Gamma'.
      has_type_cases (induction H) Case;
        intros Gamma' Heqv...
      Case "T_Var".
        apply T_Var... rewrite <- Heqv...
      Case "T_Abs".
        apply T_Abs... apply IHhas_type. intros x0 Hafi.
        unfold extend. remember (beq_id x x0) as e.
        destruct e...
      Case "T_App".
        apply T_App with T1...
      Case "T_RCons".
        apply T_RCons...  Qed.

    Lemma free_in_context : forall x t T Gamma,
       appears_free_in x t ->
       has_type Gamma t T ->
       exists T', Gamma x = Some T'.
    Proof with eauto.
      intros x t T Gamma Hafi Htyp.
      has_type_cases (induction Htyp) Case; subst; inversion Hafi; subst...
      Case "T_Abs".
        destruct (IHHtyp H5) as [T Hctx]. exists T.
        unfold extend in Hctx. apply not_eq_beq_id_false in H3.
        rewrite H3 in Hctx...  Qed.

保存
^^^^

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S  ->
         has_type empty v U   ->
         has_type Gamma (subst x v t) S.
    Proof with eauto.
      intros Gamma x U v t S Htypt Htypv.
      generalize dependent S. generalize dependent Gamma.
      tm_cases (induction t) Case; intros; simpl.
      Case "tm_var".
        rename i into y.
        destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].
        unfold extend in Hctx.
        remember (beq_id x y) as e. destruct e...
        SCase "x=y".
          apply beq_id_eq in Heqe. subst.
          inversion Hctx; subst. clear Hctx.
          apply context_invariance with empty...
          intros x Hcontra.
          destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
          inversion HT'.
        SCase "x<>y".
          destruct (subtype__wf _ _ Hsub)...
      Case "tm_app".
        destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
        eapply T_App...
      Case "tm_abs".
        rename i into y. rename t into T1.
        destruct (typing_inversion_abs _ _ _ _ _ Htypt)
          as [T2 [Hsub Htypt2]].
        destruct (subtype__wf _ _ Hsub) as [Hwf1 Hwf2].
        inversion Hwf2. subst.
        apply T_Sub with (ty_arrow T1 T2)... apply T_Abs...
        remember (beq_id x y) as e. destruct e.
        SCase "x=y".
          eapply context_invariance...
          apply beq_id_eq in Heqe. subst.
          intros x Hafi. unfold extend.
          destruct (beq_id y x)...
        SCase "x<>y".
          apply IHt. eapply context_invariance...
          intros z Hafi. unfold extend.
          remember (beq_id y z) as e0. destruct e0...
          apply beq_id_eq in Heqe0. subst.
          rewrite <- Heqe...
      Case "tm_proj".
        destruct (typing_inversion_proj _ _ _ _ Htypt)
          as [T [Ti [Hget [Hsub Htypt1]]]]...
      Case "tm_rnil".
        eapply context_invariance...
        intros y Hcontra. inversion Hcontra.
      Case "tm_rcons".
        destruct (typing_inversion_rcons _ _ _ _ _ Htypt) as
          [Ti [Tr [Hsub [HtypTi [Hrcdt2 HtypTr]]]]].
        apply T_Sub with (ty_rcons i Ti Tr)...
        apply T_RCons...
        SCase "record_ty Tr".
          apply subtype__wf in Hsub. destruct Hsub. inversion H0...
        SCase "record_tm (subst x v t2)".
          inversion Hrcdt2; subst; simpl...  Qed.

    Theorem preservation : forall t t' T,
         has_type empty t T  ->
         t ==> t'  ->
         has_type empty t' T.
    Proof with eauto.
      intros t t' T HT.
      remember empty as Gamma. generalize dependent HeqGamma.
      generalize dependent t'.
      has_type_cases (induction HT) Case;
        intros t' HeqGamma HE; subst; inversion HE; subst...
      Case "T_App".
        inversion HE; subst...
        SCase "ST_AppAbs".
          destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
          apply substitution_preserves_typing with T...
      Case "T_Proj".
        destruct (lookup_field_in_value _ _ _ _ H2 HT H)
          as [vi [Hget Hty]].
        rewrite H4 in Hget. inversion Hget. subst...
      Case "T_RCons".
        eauto using step_preserves_record_tm.  Qed.

``preservation``\ の非形式的証明:

定理:``t``\ 、\ ``t'``\ が項で\ ``T``\ が型であり\ ``empty |- t : T``\ かつ\ ``t ==> t'``\ ならば、\ ``empty |- t' : T``\ である。

証明:``t``\ と\ ``T``\ が\ ``empty |- t : T``\ であるとする。\ ``t'``\ を特化しないまま、型付け導出の構造についての帰納法で証明を進める。\ ``T_Var``\ の場合は前と同様考える必要はない。コンテキストが空だからである。

-  もし導出の最後ステップで使った規則が\ ``T_App``\ ならば、
   項\ ``t1``t2``\ と型\ ``T1``T2``\ があり、\ ``t = t1 t2``\ 、\ ``T = T2``\ 、\ ``empty |- t1 : T1 -> T2``\ 、\ ``empty |- t2 : T1``\ である。
   ステップ関係の定義を見ることにより、\ ``t1 t2``\ がステップを進める方法は3通りであることがわかる。\ ``ST_App1``\ と\ ``ST_App2``\ の場合は型付け導出の帰納法の仮定と\ ``T_App``\ を使うことで、すぐに証明が完了する。
   そうではなく\ ``ST_AppAbs``\ により\ ``t1 t2``\ がステップを進めるとする。すると、ある型\ ``S``\ と項\ ``t12``\ について\ ``t1 = \x:S.t12``\ かつ\ ``t' = [t2/x``\ t12]となる。
   補題\ ``abs_arrow``\ より、\ ``T1 <: S``\ かつ\ ``x:S1 |- s2 : T2``\ であるから、補題\ ``substitution_preserves_typing``\ より\ ``empty |- [t2/x``\ t12
   : T2]となり、これが求める結果である。

-  もし導出の最後ステップで使った規則が\ ``T_Proj``\ ならば、
   項\ ``tr``\ 、型\ ``Tr``\ 、ラベル\ ``i``\ が存在して\ ``t = tr.i``\ かつ\ ``empty |- tr : Tr``\ かつ\ ``ty_lookup i Tr = Some T``\ となる。
   型付け導出の帰納仮定より、任意の項\ ``tr'``\ について、\ ``tr ==> tr'``\ ならば\ ``empty |- tr' Tr``\ である。ステップ関係の定義より、射影がステップを進める方法は2つである。\ ``ST_Proj1``\ の場合は帰納仮定からすぐに証明される。
   そうではなく\ ``tr.i``\ のステップが\ ``ST_ProjRcd``\ による場合、\ ``tr``\ は値であり、ある項\ ``vi``\ があって\ ``tm_lookup i tr = Some vi``\ かつ\ ``t' = vi``\ となる。しかし補題\ ``lookup_field_in_value``\ より\ ``empty |- vi : Ti``\ となるが、これが求める結果である。

-  もし導出の最後ステップで使った規則が\ ``T_Sub``\ ならば、型\ ``S``\ が存在して\ ``S <: T``\ かつ\ ``empty |- t : S``\ となる。型付け導出の帰納法の仮定と\ ``T_Sub``\ の適用により結果がすぐに得られる。

-  もし導出の最後ステップで使った規則が\ ``T_RCons``\ ならば、
   項\ ``t1``tr``\ 、型\ ``T1 Tr``\ 、ラベル\ ``i``\ が存在して\ ``t = {i=t1, tr}``\ 、\ ``T = {i:T1, Tr}``\ 、\ ``record_tm tr``\ 、\ ``record_tm Tr``\ 、\ ``empty |- t1 : T1``\ 、\ ``empty |- tr : Tr``\ となる。
   ステップ関係の定義より、\ ``t``\ は\ ``ST_Rcd_Head``\ または\ ``ST_Rcd_Tail``\ によってステップを進めたはずである。\ ``ST_Rcd_Head``\ の場合、\ ``t1``\ の型付け導出についての帰納仮定と\ ``T_RCons``\ より求める結果が得られる。\ ``ST_Rcd_Tail``\ の場合、\ ``tr``\ の型付け導出についての帰納仮定、\ ``T_RCons``\ 、および\ ``step_preserves_record_tm``\ 補題の使用から求める結果が得られる。

型付けの練習問題
~~~~~~~~~~~~~~~~

練習問題: ★★, optional (variations)
'''''''''''''''''''''''''''''''''''

この問題のそれぞれの部分は、レコードとサブタイプを持つSTLCの定義を変更する別々の方法を表しています。(これらの変更は累積的ではありません。それぞれの部分はもともとの言語から始めます。)それぞれの部分について、(進行、保存の)性質のうち成立するものをリストアップしなさい。また、成立しない性質について、反例を挙げなさい。

-  次の型付け規則を追加する:

   ::

                               Gamma |- t : S1->S2
                       S1 <: T1      T1 <: S1     S2 <: T2
                       -----------------------------------              (T_Funny1)
                               Gamma |- t : T1->T2

-  次の簡約規則を追加する:

   ::

                                ------------------                     (ST_Funny21)
                                {} ==> (\x:Top. x)

-  次のサブタイプ規則を追加する:

   ::

                                  --------------                        (S_Funny3)
                                  {} <: Top->Top

-  次のサブタイプ規則を追加する:

   ::

                                  --------------                        (S_Funny4)
                                  Top->Top <: {}

-  次の評価規則を追加する:

   ::

                                -----------------                      (ST_Funny5)
                                ({} t) ==> (t {})

-  上と同じ評価規則と新しい型付け規則を追加する:

   ::

                                -----------------                      (ST_Funny5)
                                ({} t) ==> (t {})

                              ----------------------                    (T_Funny6)
                              empty |- {} : Top->Top

-  関数型についてのサブタイプ規則を次のものに変更する:

   ::

                             S1 <: T1       S2 <: T2
                             -----------------------                    (S_Arrow')
                                  S1->S2 <: T1->T2

☐
