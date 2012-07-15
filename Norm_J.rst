Norm\_J: STLCの正規化
=====================

(この章はオプションです。)

この章では、単純型付きラムダ計算の別の基本的な理論的性質を検討します。型付けされるプログラムは有限回のステップで停止することが保証されるという事実です。つまり、すべての型付けされた項は正規化可能(*normalizable*)です。

ここまで考えてきた型安全性とは異なり、正規化性は本格的なプログラミング言語には拡張されません。なぜなら、本格的な言語ではほとんどの場合、単純型付きラムダ計算に、(MoreStlc\_J章で議論したような)一般再帰や再帰型が拡張され、停止しないプログラムが書けるようになっているからです。しかし、正規化性の問題は「型のレベル」で再度現れます。それが現れるのは、F\_ωのようなラムダ計算の多相バージョンの、メタ理論を考えるときです。F\_ωでは、型の言語は単純型付きラムダ計算のコピーを効果的に包括しており、型チェックアルゴリズムの停止性は、型の式の「正規化」操作が停止することが保証されていることに依拠しています。

正規化の証明を学習する別の理由は、それが、(ここでやっているように)論理的関係の基本的証明テクニックを含むような型理論の文献において、見るべき一番美しい---そして刺激的な---数学だからです。

ここで考える計算は、基本型\ ``bool``\ と対を持つ単純型付きラムダ計算です。ここでは\ ``bool``\ を未解釈基本型として扱う基本ラムダ計算項の処理を細部まで示します。ブール演算と対の拡張は読者に残しておきます。基本計算においてさえ、正規化は証明が完全に自明ということはありません。なぜなら、項の各簡約は部分項のリデックスを複製することがあるからです。

練習問題: ★
'''''''''''

型付けされた項のサイズについての素直な帰納法で正規化性を証明しようとしたとき、どこで失敗するでしょうか？

☐

言語
----

関係する言語の定義から始めます。MoreStlc\_J章のものと同様です。そして、型の保存とステップの決定性を含む結果も成立します。(進行は使いません。)正規化の節まで飛ばしても構いません...

構文と操作的意味
^^^^^^^^^^^^^^^^

::

    Inductive ty : Type :=
      | ty_Bool : ty
      | ty_arrow : ty -> ty -> ty
      | ty_prod  : ty -> ty -> ty
    .

    Tactic Notation "ty_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ty_Bool" | Case_aux c "ty_arrow" | Case_aux c "ty_prod" ].

    Inductive tm : Type :=

置換
^^^^

::

    Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
      match t with
      | tm_var y => if beq_id x y then s else t
      | tm_abs y T t1 =>  tm_abs y T (if beq_id x y then t1 else (subst x s t1))
      | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
      | tm_pair t1 t2 => tm_pair (subst x s t1) (subst x s t2)
      | tm_fst t1 => tm_fst (subst x s t1)
      | tm_snd t1 => tm_snd (subst x s t1)
      | tm_true => tm_true
      | tm_false => tm_false
      | tm_if t0 t1 t2 => tm_if (subst x s t0) (subst x s t1) (subst x s t2)
      end.

簡約
^^^^

::

    Inductive value : tm -> Prop :=
      | v_abs : forall x T11 t12,
          value (tm_abs x T11 t12)
      | v_pair : forall v1 v2,
          value v1 ->
          value v2 ->
          value (tm_pair v1 v2)
      | v_true : value tm_true
      | v_false : value tm_false
    .

    Hint Constructors value.

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

型付け
^^^^^^

::

    Definition context := partial_map ty.

    Inductive has_type : context -> tm -> ty -> Prop :=

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

保存
^^^^

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S  ->
         has_type empty v U   ->
         has_type Gamma (subst x v t) S.
    Proof with eauto.

          apply substitution_preserves_typing with T1...
          inversion HT1...
      Case "T_Fst".
        inversion HT...
      Case "T_Snd".
        inversion HT...
    Qed.

☐

決定性
^^^^^^

::

    Lemma step_deterministic :
       partial_function step.
    Proof with eauto.
       unfold partial_function.

ここを埋めなさい

::

    Admitted.

正規化
------

ここからが本当の正規化の証明です。

ゴールはすべての型付けされた項が正規形になることを証明することです。実際のところ、もうちょっと強いことを証明した方が便利です。つまり、すべての型付けされた項が値になるということです。この強い方は、いずれにしろ弱い方から進行補題を使って得ることができますが(なぜでしょう？)、最初から強い方を証明すれば進行性は必要ありません。そして、進行性を再び証明することは上では行いませんでした。

これがキーとなる定義です:

::

    Definition halts  (t:tm) : Prop :=  exists t', t ==>* t' /\  value t'.

あたりまえの事実:

::

    Lemma value_halts : forall v, value v -> halts v.
    Proof.
      intros v H. unfold halts.
      exists v. split.
      apply rsc_refl.
      assumption.
    Qed.

正規化の証明のキーとなる問題は、(多くの帰納法による証明と同様に)十分な強さの帰納法の仮定を見つけることです。このために、それぞれの型\ ``T``\ に対して型\ ``T``\ の閉じた項の集合\ ``R_T``\ を定義することから始めます。これらの集合を関係\ ``R``\ を使って定め、\ ``t``\ が\ ``R_T``\ の要素であることを\ ``R T t``\ と書きます。(集合\ ``R_T``\ はしばしば飽和集合(*saturated
sets*)あるいは簡約可能性候補(*reducibility candidates*)と呼ばれます。)

基本言語に対する\ ``R``\ の定義は以下の通りです:

-  ``R bool t``\ とは、\ ``t``\ が型\ ``bool``\ の閉じた項で\ ``t``\ が値になることである
-  ``R (T1 -> T2) t``\ とは、\ ``t``\ が型\ ``T1 -> T2``\ の閉じた項で、\ ``t``\ が値になり、かつ、\ ``R T1 s``\ となる任意の項\ ``s``\ について、\ ``R T2 (t s)``\ となることである。

この定義は必要な強化された帰納法の仮定を与えます。最初のゴールはすべてのプログラム(つまり、基本型のすべての閉じた項)が停止することを示すことです。しかし、基本型の閉じた項は関数型の部分項を含むこともできるので、これらについても性質を知ることが必要です。さらに、これらの部分項が停止することを知るだけでは不十分です。なぜなら、正規化された関数を正規化された引数へ適用すると置換が行われるため、さらに評価ステップが発生する可能性があるからです。これから関数型の項についてより強い条件が必要です。つまり、自分自身が停止するだけでなく、停止する引数に適用されると停止する結果にならなければならないという条件です。

``R``\ の形は論理的関係(*logical
relations*)証明テクニックの特徴です。(ここで扱うのは単項関係のみなので、おそらく論理的述語(*logical
predicates*)という方がより適切でしょう。)型\ ``A``\ のすべての閉じた項についてある性質\ ``P``\ を証明したい場合、型についての帰納法により、型\ ``A``\ のすべての項が性質\ ``P``\ を「持ち」、型\ ``A->A``\ のすべての項が性質\ ``P``\ を「保存し」、型\ ``(A->A)->(A->A)``\ のすべての項が性質\ ``P``\ を「保存することを保存し」、...ということを証明していきます。このために型をインデックスとする述語の族を定義します。基本型\ ``A``\ に対しては、述語は単に\ ``P``\ です。関数型に対しては、述語は、その関数が入力の型の述語を満たす値を出力の型の述語を満たす値に写像することを言うものです。

Coqで\ ``R``\ の定義を形式化しようとするとき、問題が生じます。一番自明な形式化は、次のようなパラメータ化された
Inductive による命題でしょう：

::

    Inductive R : ty -> tm -> Prop :=
    | R_bool : forall b t, has_type empty t ty_Bool ->
                    halts t ->
                    R ty_Bool t
    | R_arrow : forall T1 T2 t, has_type empty t (ty_arrow T1 T2) ->
                    halts t ->
                    (forall s, R T1 s -> R T2 (tm_app t s)) ->
                    R (ty_arrow T1 T2) t.

残念ながらCoqはこの定義を受け付けません。なぜなら帰納的定義の\_strict
positivity requirement\_を満たさないからです。\ *strict positivity
requirement\_とは、定義される型がコンストラクタ引数の型の矢印の左に現れてはいけないというものです。ここで、この規則を破っているのは、\ ``R_arrow``\ の第3引数、すなわち、\ ``(forall s, R T1 s -> R TS (tm_app t s))``\ の、特に\ ``R T1 s``\ の部分です。(一番外側のコンストラクタ引数を分離している矢印は規則の対象外です。そうでなければ、純粋な帰納的述語はまったく定義できません!)この規則がある理由は、正ではない再帰(non-positive
recursion)を使って定義された型は停止しない関数を作るのに使うことができ、それがCoqの論理的健全性を脅かすからです。ここで定義しようとしている関係が完全に問題ないものであるにもかかわらず、*\ strict
positivity requirement\_のテストを通らないので、Coqはこれを拒否します。

幸い、\ ``Fixpoint``\ を使うと\ ``R``\ が定義できます:

::

    Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
      has_type empty t T /\ halts t /\
      (match T with
       | ty_Bool  => True
       | ty_arrow T1 T2 => (forall s, R T1 s -> R T2 (tm_app t s))

ここを埋めなさい

::

    | ty_prod T1 T2 => False

この定義からすぐに導かれることとして、すべての集合\ ``R_T``\ について、そのすべての要素は停止して値となり、また型\ ``T``\ について閉じていることが言えます:

::

    Lemma R_halts : forall {T} {t}, R T t -> halts t.
    Proof.
      intros. destruct T; unfold R in H; inversion H; inversion H1;  assumption.
    Qed.


    Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
    Proof.
      intros. destruct T; unfold R in H; inversion H; inversion H1; assumption.
    Qed.

さて、メインの結果に進みます。すべての型\ ``T``\ の項が\ ``R_T``\ の要素であることを示すことです。\ ``R_halts``\ と組み合わせると、すべての型付けされる項は停止して値になることが示されます。

``R_T``\ の要素であるか否かは評価によって変化しない
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

一種の強保存性を示す予備的補題から始めます。\ ``R_T``\ の要素であるか否かは評価によって「不変」(*invariant*)であるという補題です。この性質は両方向が必要です。つまり、\ ``R_T``\ の項がステップを進めても\ ``R_T``\ にあることを示すことと、ステップ後\ ``R_T``\ の要素になる任意の項が最初から\ ``R_T``\ であることを示すことです。

一番最初に、簡単な予備的補題です。前向き方法については、言語が決定性を持つという事実に証明が依存していることに注意します。この補題は非決定的な言語でも成立するかもしれませんが、証明はより難しくなるでしょう!

::

    Lemma step_preserves_halting : forall t t', (t ==> t') -> (halts t <-> halts t').
    Proof.
     intros t t' ST.  unfold halts.
     split.
     Case "->".
      intros [t'' [STM V]].
      inversion STM; subst.
       apply ex_falso_quodlibet.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
       rewrite (step_deterministic _ _ _ ST H). exists t''. split; assumption.
     Case "<-".
      intros [t'0 [STM V]].
      exists t'0. split; eauto.
    Qed.

さてメインの補題ですが、2つの方向に対応する2つの部分から成ります。それぞれは型\ ``T``\ の構造についての帰納法で進みます。事実、ここでは型の有限性を本質的な部分で使っています。

ステップを進んだ結果が\ ``R_T``\ の要素であるためには型\ ``T``\ を持つことが必要です。このことは、前向き方向については、もともとの型保存から得られます。

::

    Lemma step_preserves_R : forall T t t', (t ==> t') -> R T t -> R T t'.
    Proof.
     induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
                   destruct Rt as [typable_empty_t [halts_t RRt]].

ここを埋めなさい

::

    Admitted.

複数ステップへの一般化については自明です:

::

    Lemma stepmany_preserves_R : forall T t t',
      (t ==>* t') -> R T t -> R T t'.
    Proof.
      intros T t t' STM; induction STM; intros.
      assumption.
      apply IHSTM. eapply step_preserves_R. apply H. assumption.
    Qed.

逆向き方向については、\ ``t``\ がステップ前に型\ ``T``\ を持つという事実を追加の仮定として加える必要があります。

::

    Lemma step_preserves_R' : forall T t t',
      has_type empty t T -> (t ==> t') -> R T t' -> R T t.
    Proof.

ここを埋めなさい

::

    Admitted.

    Lemma stepmany_preserves_R' : forall T t t',
      has_type empty t T -> (t ==>* t') -> R T t' -> R T t.
    Proof.
      intros T t t' HT STM.
      induction STM; intros.
        assumption.
        eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
        eapply preservation;  eauto. auto.
    Qed.

``R_T``\ に含まれる型\ ``T``\ の項の閉じたインスタンス
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

これから、型\ ``T``\ のすべての項が\ ``R_T``\ に含まれることを示すことに取りかかります。ここで使う帰納法は型付け導出についてのものです(もし、型付け導出の帰納法と全く関係がない型付けされた項についての証明があったら、驚くでしょう!)。ここで技術的に難しいのは、関数抽象の場合だけです。帰納法で議論していることから、項\ ``tm_abs x T1 t2``\ が\ ``R_(T1->T2)``\ に属していることを示すことには\ ``t2``\ が\ ``R_(T2)``\ に属するという帰納法の仮定を含みます。しかし\ ``R_(T2)``\ は「閉じた」項の集合である一方、\ ``t2``\ は\ ``x``\ を自由変数として含む可能性があるので、これは筋が通りません。

この問題は帰納法の仮定を適度に一般化するという標準的なトリックを使うことで解決されます。閉じた項を含む主張を証明する代わりに、開いた項\ ``t``\ のすべての閉じたインスタンス(*instances*)をカバーするように一般化します。非形式的には、補題の主張は次のようになります:

もし\ ``x1:T1,..xn:Tn |- t : T``\ かつ、\ ``v1,...,vn``\ が\ ``R T1 v1``,\ ``R T2 v2``,
...,\ ``R Tn vn``\ となる値ならば、\ ``R T ([v1/x1``v2/x2``...\ ``vn/xn``\ t)]
である。

証明は、型付け\ ``x1:T1,..xn:Tn |- t : T``\ の導出についての帰納法で進みます。一番興味深いのは、関数抽象の場合です。

多重置換、多重拡張、インスタンス化
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

しかしながら、主張と補題の証明の形式化に進む前に、項\ ``t``\ の多重置換(*multiple\_substitutions)と型付けコンテキストの多重拡張(*\ multiple\_
extensions)についての事実を扱う、ある(かなり退屈な)機構を構築する必要があります。特に、置換が現れる順序とそれらの相互関係を正確にする必要があります。これらの詳細は非形式的な紙の証明では単に省略されるのが通常です。しかしもちろん、Coqはそうはしません。ここでは閉じた項を置換していることから、1つの置換が他の置換によってできた項に影響するかどうかを心配する必要はありません。しかしそれでも置換の順序については考慮する必要があります。なぜなら、\ ``x1,...xn``\ に同じ識別子が複数回出現しそれらが違う\ ``vi``\ や\ ``Ti``\ と関連付けされている可能性があるからです。

すべてを正確にするために、環境は左から右へ拡張されることとし、多重置換は右から左へ実行されることとします。これが整合的であることを見るために、\ ``...,y:bool,...,y:nat,...``\ と書かれる環境と、対応する\ ``...[(tm_bool true)/y``...\ ``(tm_nat 3)/y``...t]と書かれる項の置換があるとします。環境は左から右に拡張されることから、\ ``y:nat``\ は\ ``y:bool``\ を隠します。置換は右から左に実行されることから、\ ``(tm_nat 3)/y``\ が最初に実行され、\ ``(tm_bool true)/y``\ は何の作用もしません。これから置換は項の型を正しく保存します。

このポイントを覚えておくと、次の定義が理解できます。

多重置換(*multisubstitution*)は置換のリストの適用結果です。置換のリストは環境と呼ばれます(*environment*)。

::

    Definition env := list (id * tm).

    Fixpoint msubst (ss:env) (t:tm) {struct ss} : tm :=
    match ss with
    | nil => t
    | ((x,s)::ss') => msubst ss' (subst x s t)
    end.

(識別子、型)の対のリストを使った型付けコンテキストの継続的拡張についても同様の機構が必要です。この型付けコンテキストを「型割当て」(*type
assignment*)と呼びます。

::

    Definition tass := list (id * ty).

    Fixpoint mextend (Gamma : context) (xts : tass) :=
      match xts with
      | nil => Gamma
      | ((x,v)::xts') => extend (mextend Gamma xts') x v
      end.

環境と型割当てに同様にはたらくいくつかの簡単な操作が必要です。

::

    Fixpoint lookup {X:Set} (k : id) (l : list (id * X)) {struct l} : option X :=
      match l with
        | nil => None
        | (j,x) :: l' =>
          if beq_id j k then Some x else lookup k l'
      end.

    Fixpoint drop {X:Set} (n:id) (nxs:list (id * X)) {struct nxs} : list (id * X) :=
      match nxs with
        | nil => nil
        | ((n',x)::nxs') => if beq_id n' n then drop n nxs' else (n',x)::(drop n nxs')
      end.

インスタンス化(*instantiation*)は型割当てと値環境を同じ定義域で結合します。この定義域の要素はRに含まれます。

::

    Inductive instantiation :  tass -> env -> Prop :=
    | V_nil : instantiation nil nil
    | V_cons : forall x T v c e, value v -> R T v -> instantiation c e -> instantiation ((x,T)::c) ((x,v)::e).

これから、これらの定義についてのいろいろな性質を証明します。

置換についてのさらなる事実
^^^^^^^^^^^^^^^^^^^^^^^^^^

最初に(もともとの)置換について、ある追加の補題が必要です。

::

    Lemma vacuous_substitution : forall  t x,
         ~ appears_free_in x t  ->
         forall t', subst x t' t = t.
    Proof with eauto.

ここを埋めなさい

::

    Admitted.

    Lemma subst_closed: forall t,
         closed t  ->
         forall x t', subst x t' t = t.
    Proof.
      intros. apply vacuous_substitution. apply H.  Qed.


    Lemma subst_not_afi : forall t x v, closed v ->  ~ appears_free_in x (subst x v t).
    Proof with eauto.

ここを埋めなさい

::

    Admitted.

多重置換の性質
^^^^^^^^^^^^^^

::

    Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
    Proof.
      induction ss.
        reflexivity.
        destruct a. simpl. rewrite subst_closed; assumption.
    Qed.

閉じた環境とは、閉じた項のみを含む環境です。

::

    Fixpoint closed_env (env:env) {struct env} :=
    match env with
    | nil => True
    | (x,t)::env' => closed t /\ closed_env env'
    end.

次は、閉じた項についての\ ``msubst``\ がどのように\ ``subst``\ や各項の形に分配されるかを特徴づける一連の補題です。

::

    Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
      msubst env (subst x v t) = subst x v (msubst (drop x env) t).
    Proof.
      induction env0; intros.
        auto.
        destruct a. simpl.
        inversion H0. fold closed_env in H2.
        remember (beq_id i x) as e; destruct e.
          apply  beq_id_eq in Heqe; subst.
            rewrite duplicate_subst; auto.
          symmetry in Heqe. apply beq_id_false_not_eq in Heqe.
          simpl. rewrite swap_subst; eauto.
    Qed.


    Lemma msubst_var:  forall ss x, closed_env ss ->
       msubst ss (tm_var x) =
       match lookup x ss with
       | Some t => t
       | None => tm_var x
      end.
    Proof.
      induction ss; intros.
        reflexivity.
        destruct a.
         simpl. destruct (beq_id i x).
          apply msubst_closed. inversion H; auto.
          apply IHss. inversion H; auto.
    Qed.

    Lemma msubst_abs: forall ss x T t,
      msubst ss (tm_abs x T t) = tm_abs x T (msubst (drop x ss) t).
    Proof.
      induction ss; intros.
        reflexivity.
        destruct a.
          simpl. destruct (beq_id i x); simpl; auto.
    Qed.

    Lemma msubst_app : forall ss t1 t2, msubst ss (tm_app t1 t2) = tm_app (msubst ss t1) (msubst ss t2).
    Proof.
     induction ss; intros.
       reflexivity.
       destruct a.
        simpl. rewrite <- IHss. auto.
    Qed.

他の項コンストラクタに対しても同様の関数が必要になるでしょう。

ここを埋めなさい

多重拡張の性質
^^^^^^^^^^^^^^

型割当てのふるまいを、対応するコンテキストのふるまいと結合する必要があります。

::

    Lemma mextend_lookup : forall (c : tass) (x:id), lookup x c = (mextend empty c) x.
    Proof.
      induction c; intros.
        auto.
        destruct a. unfold lookup, mextend, extend. destruct (beq_id i x); auto.
    Qed.

    Lemma mextend_drop : forall (c: tass) Gamma x x',
           mextend Gamma (drop x c) x' = if beq_id x x' then Gamma x' else mextend Gamma c x'.
       induction c; intros.
          destruct (beq_id x x'); auto.
          destruct a. simpl.
          remember (beq_id i x) as e; destruct e.
            apply beq_id_eq in Heqe; subst. rewrite IHc.
                remember (beq_id x x') as e; destruct e.  auto. unfold extend. rewrite <- Heqe. auto.
            simpl.  unfold extend.  remember (beq_id i x') as e; destruct e.
                apply beq_id_eq in Heqe0; subst.
                                  remember (beq_id x x') as e; destruct e.
                      apply beq_id_eq in Heqe0; subst.  rewrite <- beq_id_refl in Heqe.  inversion Heqe.
                      auto.
                auto.
    Qed.

インスタンス化の性質
^^^^^^^^^^^^^^^^^^^^

以下は簡単です。

::

    Lemma instantiation_domains_match: forall {c} {e},
      instantiation c e -> forall {x} {T}, lookup x c = Some T -> exists t, lookup x e = Some t.
    Proof.
      intros c e V. induction V; intros x0 T0 C.
        solve by inversion .
        simpl in *.
        destruct (beq_id x x0); eauto.
    Qed.

    Lemma instantiation_env_closed : forall c e,  instantiation c e -> closed_env e.
    Proof.
      intros c e V; induction V; intros.
        econstructor.
        unfold closed_env. fold closed_env.
        split.  eapply typable_empty__closed. eapply R_typable_empty. eauto.
            auto.
    Qed.

    Lemma instantiation_R : forall c e, instantiation c e ->
                            forall x t T, lookup x c = Some T ->
                                          lookup x e = Some t -> R T t.
    Proof.
      intros c e V. induction V; intros x' t' T' G E.
        solve by inversion.
        unfold lookup in *.  destruct (beq_id x x').
          inversion G; inversion E; subst.  auto.
          eauto.
    Qed.

    Lemma instantiation_drop : forall c env,
      instantiation c env -> forall x, instantiation (drop x c) (drop x env).
    Proof.
      intros c e V. induction V.
        intros.  simpl.  constructor.
        intros. unfold drop. destruct (beq_id x x0); auto. constructor; eauto.
    Qed.

stepmany(``==>*``)についての合同補題
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

これらのいくつかだけが必要になります。必要が生じた時点で追加しなさい。

::

    Lemma stepmany_App2 : forall v t t',
      value v -> (t ==>* t') -> (tm_app v t) ==>* (tm_app v t').
    Proof.
      intros v t t' V STM. induction STM.
       apply rsc_refl.
       eapply rsc_step.
         apply ST_App2; eauto.  auto.
    Qed.

ここを埋めなさい

R補題
^^^^^

最後にすべてをまとめます。

置換についての型付けの保存についてのキーとなる補題は、多重置換に対応する形にすることができます:

::

    Lemma msubst_preserves_typing : forall c e,
         instantiation c e ->
         forall Gamma t S, has_type (mextend Gamma c) t S ->
         has_type Gamma (msubst e t) S.
    Proof.
      induction 1; intros.
        simpl in H. simpl. auto.
        simpl in H2.  simpl.
        apply IHinstantiation.
        eapply substitution_preserves_typing; eauto.
        apply (R_typable_empty H0).
    Qed.

そして一番最後に、メインの補題です。

::

    Lemma msubst_R : forall c env t T,
      has_type (mextend empty c) t T -> instantiation c env -> R T (msubst env t).
    Proof.
      intros c env0 t T HT V.
      generalize dependent env0.

ここを埋めなさい

::

    Admitted.

正規化定理
^^^^^^^^^^

::

    Theorem normalization : forall t T, has_type empty t T -> halts t.
    Proof.
      intros.
      replace t with (msubst nil t).
      eapply R_halts.
      eapply msubst_R; eauto. instantiate (2:= nil). eauto.
      eapply V_nil.
      auto.
    Qed.

