Records\_J: STLCにレコードを追加する
====================================

レコードを追加する
------------------

``MoreStlc_J.v``\ で、レコードを、直積のネストされた使用の構文糖衣として扱う方法を見ました。これは簡単な例にはよいです。しかし、エンコードは非形式的です。(現実的に、もしこの方法でレコードを本当に扱うならパーサ内で実行されることになりますが、パーサはここでは省いています。)そしていずれにしろ、あまり効率的ではありません。これから、レコードを言語の第一級(first-class)のメンバーとしてはどのように扱えるのか見るのも興味があるところです。

前の非形式的定義を思い出してみましょう:

構文:

::

           t ::=                          項:
               | ...
               | {i1=t1, ..., in=tn}         レコード
               | t.i                         射影

           v ::=                          値:
               | ...
               | {i1=v1, ..., in=vn}         レコード値

           T ::=                          型:
               | ...
               | {i1:T1, ..., in:Tn}         レコード型

簡約:

::

                                     ti ==> ti'                            (ST_Rcd)
        --------------------------------------------------------------------
        {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                                     t1 ==> t1'
                                   --------------                        (ST_Proj1)
                                   t1.i ==> t1'.i

                              -------------------------                (ST_ProjRcd)
                              {..., i=vi, ...}.i ==> vi

型付け:

::

                   Gamma |- t1 : T1     ...     Gamma |- tn : Tn
                 --------------------------------------------------         (T_Rcd)
                 Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                           Gamma |- t : {..., i:Ti, ...}
                           -----------------------------                   (T_Proj)
                                 Gamma |- t.i : Ti

レコードを形式化する
--------------------

::

    Module STLCExtendedRecords.

構文と操作的意味
^^^^^^^^^^^^^^^^

レコード型の構文を形式化する最も明らかな方法はこうです:

::

    Module FirstTry.

    Definition alist (X : Type) := list (id * X).

    Inductive ty : Type :=
      | ty_base     : id -> ty
      | ty_arrow    : ty -> ty -> ty
      | ty_rcd      : (alist ty) -> ty.

残念ながら、ここで Coq
の限界につきあたりました。この型は期待する帰納原理を自動的には提供してくれないのです。\ ``ty_rcd``\ の場合の帰納法の仮定はリストの\ ``ty``\ 要素について何の情報も提供してくれないのです。このせいで、行いたい証明に対してこの型は役に立たなくなっています。

::

    (* Check ty_ind.
       ====>
        ty_ind :
          forall P : ty -> Prop,
            (forall i : id, P (ty_base i)) ->
            (forall t : ty, P t -> forall t0 : ty, P t0 -> P (ty_arrow t t0)) ->
            (forall a : alist ty, P (ty_rcd a)) ->    (* ??? *)
            forall t : ty, P t
    *)

    End FirstTry.

より良い帰納法の原理をCoqから取り出すこともできます。しかしそれをやるための詳細はあまりきれいではありません。またCoqが単純な\ ``Inductive``\ 定義に対して自動生成したものほど直観的でもありません。

幸い、レコードについて、別の、ある意味より単純でより自然な形式化方法があります。既存の\ ``list``\ 型の代わりに、型の構文にリストのコンストラクタ("nil"と"cons")を本質的に含めてしまうという方法です。

::

    Inductive ty : Type :=
      | ty_base : id -> ty
      | ty_arrow : ty -> ty -> ty
      | ty_rnil : ty
      | ty_rcons : id -> ty -> ty -> ty.

    Tactic Notation "ty_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ty_base" | Case_aux c "ty_arrow"
      | Case_aux c "ty_rnil" | Case_aux c "ty_rcons" ].

同様に、項のレベルで、空レコードに対応するコンストラクタ\ ``tm_rnil``\ と、フィールドのリストの前に1つのフィールドを追加するコンストラクタ\ ``tm_rcons``\ を用意します。

::

    Inductive tm : Type :=
      | tm_var : id -> tm
      | tm_app : tm -> tm -> tm
      | tm_abs : id -> ty -> tm -> tm


      (* レコード *)

    | tm_proj : tm -> id -> tm
      | tm_rnil :  tm
      | tm_rcons : id -> tm -> tm -> tm.

    Tactic Notation "tm_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
      | Case_aux c "tm_proj" | Case_aux c "tm_rnil" | Case_aux c "tm_rcons" ].

Some variables, for examples...

いくつかの変数、例えば...

::

    Notation a := (Id 0).
    Notation f := (Id 1).
    Notation g := (Id 2).
    Notation l := (Id 3).
    Notation A := (ty_base (Id 4)).
    Notation B := (ty_base (Id 5)).
    Notation k := (Id 6).
    Notation i1 := (Id 7).
    Notation i2 := (Id 8).

``{ i1:A }``

::

    (* Check (ty_rcons i1 A ty_rnil). *)

``{ i1:A->B, i2:A }``

::

    (* Check (ty_rcons i1 (ty_arrow A B)
               (ty_rcons i2 A ty_rnil)). *)

Well-Formedness(正しい形をしていること、整式性)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

レコードの抽象構文を(リストから nil/cons
構成に)一般化すると、次のような奇妙な型を書くことがができるようになります。

::

    Definition weird_type := ty_rcons X A B.

ここでレコード型の「後部」は実際にはレコード型ではありません!

以降で型ジャッジメントを、\ ``weird_type``\ のようなill-formedの(正しくない形の)型が項に割当てられないように構成します。これをサポートするために、レコード型と項を識別するための\ ``record_ty``\ と\ ``record_tm``\ 、およびill-formedの型を排除するための\ ``well_formed_ty``\ を定義します。

最初に、型がレコード型なのは、それの一番外側のレベルが\ ``ty_rnil``\ と\ ``ty_rcons``\ だけを使って構築されたもののときです。

::

    Inductive record_ty : ty -> Prop :=
      | rty_nil :
            record_ty ty_rnil
      | rty_cons : forall i T1 T2,
            record_ty (ty_rcons i T1 T2).

同様に、項がレコード項であるのは、\ ``tm_rnil``\ と\ ``tm_rcons``\ から構築されたもののときです。

::

    Inductive record_tm : tm -> Prop :=
      | rtm_nil :
            record_tm tm_rnil
      | rtm_cons : forall i t1 t2,
            record_tm (tm_rcons i t1 t2).

``record_ty``\ と\ ``record_tm``\ は再帰的ではないことに注意します。両者は、一番外側のコンストラクタだけをチェックします。一方\ ``well_formed_ty``\ は型全体がwell-formedか(正しい形をしているか)、つまり、レコードのすべての後部(``ty_rcons``\ の第2引数)がレコードであるか、を検証します。

もちろん、型だけでなく項についても、ill-formedの可能性を考慮しなければなりません。しかし、別途\ ``well_formed_tm``\ を用意しなくても、ill-formed項は型チェックが排除します。なぜなら、型チェックが既に項の構成を調べるからです。

LATER : should they fill in part of this as an exercise? Wedidn't give
rules for it above

(訳注：この"LATER"部分が誰向けに何を言おうとしているのかはっきりしないので、訳さずに残しておきました。)

::

    Inductive well_formed_ty : ty -> Prop :=
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
      | tm_rcons i t1 tr1 => tm_rcons i (subst x s t1) (subst x s tr1)
      end.

簡約
^^^^

次に言語の値を定義します。レコードが値であるのは、そのフィールドがすべて値であるときです。

::

    Inductive value : tm -> Prop :=
      | v_abs : forall x T11 t12,
          value (tm_abs x T11 t12)
      | v_rnil : value tm_rnil
      | v_rcons : forall i v1 vr,
          value v1 ->
          value vr ->
          value (tm_rcons i v1 vr).

    Hint Constructors value.

レコード型またはレコード項から1つのフィールドを取り出すユーティリティ関数です:

::

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

``step``\ 関数は(射影規則について)項レベルのlookup関数を使います。一方、型レベルのlookupは\ ``has_type``\ で必要になります。

::

    Reserved Notation "t1 '==>' t2" (at level 40).

    Inductive step : tm -> tm -> Prop :=
      | ST_AppAbs : forall x T11 t12 v2,
             value v2 ->
             (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
      | ST_App1 : forall t1 t1' t2,
             t1 ==> t1' ->
             (tm_app t1 t2) ==> (tm_app t1' t2)
      | ST_App2 : forall v1 t2 t2',
             value v1 ->
             t2 ==> t2' ->
             (tm_app v1 t2) ==> (tm_app v1 t2')
      | ST_Proj1 : forall t1 t1' i,
            t1 ==> t1' ->
            (tm_proj t1 i) ==> (tm_proj t1' i)
      | ST_ProjRcd : forall tr i vi,
            value tr ->
            tm_lookup i tr = Some vi ->
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
      | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd"
      | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail" ].

    Notation stepmany := (refl_step_closure step).
    Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

    Hint Constructors step.

型付け
^^^^^^

::

    Definition context := partial_map ty.

次に型付け規則を定義します。これは上述の推論規則をほぼそのまま転写したものです。大きな違いは\ ``well_formed_ty``\ の使用だけです。非形式的な表記では、well-formedレコード型だけを許す文法を使ったので、別のチェックを用意する必要はありませんでした。

ここでは、\ ``has_type Gamma t T``\ が成立するときは常に\ ``well_formed_ty T``\ が成立するようにしたいところです。つまり、\ ``has_type``\ は項にill-formed型を割当てることはないようにするということです。このことを後で実際に証明します。

しかしながら\ ``has_type``\ の定義を、\ ``well_formed_ty``\ を不必要に使って取り散らかしたくはありません。その代わり\ ``well_formed_ty``\ によるチェックを必要な所だけに配置します。ここで、必要な所というのは、\ ``has_type``\ の帰納的呼び出しによっても未だ型のwell-formed性のチェックが行われていない所のことです。

例えば、\ ``T_Var``\ の場合、\ ``well_formed_ty T``\ をチェックします。なぜなら、\ ``T``\ の形がwell-formedであることを調べる帰納的な\ ``has_type``\ の呼び出しがないからです。同様に\ ``T_Abs``\ の場合、\ ``well_formed_ty T11``\ の証明を必要とします。なぜなら、\ ``has_type``\ の帰納的呼び出しは\ ``T12``\ がwell-formedであることだけを保証するからです。

読者が記述しなければならない規則の中で\ ``well_formed_ty``\ チェックが必要なのは、\ ``tm_nil``\ の場合だけです。

::

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

例
~~

練習問題: ★★ (examples)
'''''''''''''''''''''''

証明を完成させなさい。

証明の中ではCoq
の自動化機能を自由に使って構いません。しかし、もし型システムがどのように動作するか確信できていないなら、最初に基本機能(特に\ ``eapply``\ ではなく\ ``apply``)を使った証明を行い、次に自動化を使ってその証明を圧縮するのがよいかもしれません。

::

    Lemma typing_example_2 :
      has_type empty
        (tm_app (tm_abs a (ty_rcons i1 (ty_arrow A A)
                          (ty_rcons i2 (ty_arrow B B)
                           ty_rnil))
                  (tm_proj (tm_var a) i2))
                (tm_rcons i1 (tm_abs a A (tm_var a))
                (tm_rcons i2 (tm_abs a B (tm_var a))
                 tm_rnil)))
        (ty_arrow B B).
    Proof.

次の事実(あるいはすぐ上の事実も!)の証明を始める前に、それが何を主張しているかを確認しなさい。

::

    Example typing_nonexample :
      ~ exists T,
          has_type (extend empty a (ty_rcons i2 (ty_arrow A A)
                                    ty_rnil))
                   (tm_rcons i1 (tm_abs a B (tm_var a)) (tm_var a))
                   T.
    Proof.

型付けの性質
~~~~~~~~~~~~

このシステムの進行と保存の証明は、純粋な単純型付きラムダ計算のものと本質的に同じです。しかし、レコードについての技術的補題を追加する必要があります。

Well-Formedness
^^^^^^^^^^^^^^^

::

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

    Lemma step_preserves_record_tm : forall tr tr',
      record_tm tr ->
      tr ==> tr' ->
      record_tm tr'.
    Proof.
      intros tr tr' Hrt Hstp.
      inversion Hrt; subst; inversion Hstp; subst; auto.
    Qed.

    Lemma has_type__wf : forall Gamma t T,
      has_type Gamma t T -> well_formed_ty T.
    Proof with eauto.
      intros Gamma t T Htyp.
      has_type_cases (induction Htyp) Case...
      Case "T_App".
        inversion IHHtyp1...
      Case "T_Proj".
        eapply wf_rcd_lookup...
    Qed.

フィールドのルックアップ
^^^^^^^^^^^^^^^^^^^^^^^^

補題:
もし\ ``empty |- v : T``\ で、かつ\ ``ty_lookup i T``\ が\ ``Some Ti``\ を返すならば,\ ``tm_lookup i v``\ はある項\ ``ti``\ について\ ``Some ti``\ を返す。ただし、\ ``has_type empty ti Ti``\ となる。

証明:
型の導出\ ``Htyp``\ についての帰納法で証明する。\ ``ty_lookup i T = Some Ti``\ であることから、\ ``T``\ はレコード型でなければならない。このことと\ ``v``\ が値であることから、ほとんどの場合は精査で除去でき、\ ``T_RCons``\ の場合だけが残る。

型導出の最後のステップが\ ``T_RCons``\ によるものであるとき、ある\ ``i0``\ 、\ ``t``\ 、\ ``tr``\ 、\ ``T``\ 、\ ``Tr``\ について\ ``t = tm_rcons i0 t tr``\ かつ\ ``T = ty_rcons i0 T Tr``\ である。

このとき2つの可能性が残る。\ ``i0 = i``\ か、そうでないかである。

-  ``i = i0``\ のとき、\ ``ty_lookup i (ty_rcons i0 T Tr) = Some Ti``\ から\ ``T = Ti``\ となる。これから\ ``t``\ 自身が定理を満たすことが言える。
-  一方、\ ``i <> i0``\ とする。すると

   ::

           ty_lookup i T = ty_lookup i Tr

かつ

::

            tm_lookup i t = tm_lookup i tr

となる。これから、帰納法の仮定より結果が得られる。

::

    Lemma lookup_field_in_value : forall v T i Ti,
      value v ->
      has_type empty v T ->
      ty_lookup i T = Some Ti ->
      exists ti, tm_lookup i v = Some ti /\ has_type empty ti Ti.
    Proof with eauto.
      intros v T i Ti Hval Htyp Hget.
      remember (@empty ty) as Gamma.
      has_type_cases (induction Htyp) Case; subst; try solve by inversion...
      Case "T_RCons".
        simpl in Hget. simpl. destruct (beq_id i i0).
        SCase "i is first".
          simpl. inversion Hget. subst.
          exists t...
        SCase "get tail".
          destruct IHHtyp2 as [vi [Hgeti Htypi]]...
          inversion Hval... Qed.

進行
^^^^

::

    Theorem progress : forall t T,
         has_type empty t T ->
         value t \/ exists t', t ==> t'.
    Proof with eauto.

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
      | afi_rhead : forall x i ti tr,
          appears_free_in x ti ->
          appears_free_in x (tm_rcons i ti tr)
      | afi_rtail : forall x i ti tr,
          appears_free_in x tr ->
          appears_free_in x (tm_rcons i ti tr).

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
        apply T_Abs... apply IHhas_type. intros y Hafi.
        unfold extend. remember (beq_id x y) as e.
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
      has_type_cases (induction Htyp) Case; inversion Hafi; subst...
      Case "T_Abs".
        destruct IHHtyp as [T' Hctx]... exists T'.
        unfold extend in Hctx.
        apply not_eq_beq_id_false in H3. rewrite H3 in Hctx...
    Qed.

保存
^^^^

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S  ->
         has_type empty v U   ->
         has_type Gamma (subst x v t) S.
    Proof with eauto.

        apply T_RCons... eapply step_preserves_record_tm...
    Qed.

☐

::

    End STLCExtendedRecords.

