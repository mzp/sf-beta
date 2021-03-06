Logic\_J: Coqにおける論理
=========================

::

    Require Export "Prop_J".

Coqの組み込み論理は非常に小さく、帰納的定義(``Inductive``)、全称記号(``forall``)、ならば(``->``)だけです。しかしそれ以外の論理演算子（かつ、または、否定、存在量化子、等号など）はこれら組み込みのものから定義できます。

全称記号 と ならば
------------------

実は、\ ``->``\ と\ ``forall``\ は 同じものです!
Coqの\ ``->``\ 記法は\ ``forall``\ の短縮記法に過ぎません。仮定に名前をつけることができることから、\ ``forall``\ 記法の方がより一般的に使われます。

例えば次の命題を考えてみましょう。

::

    Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

もしもこの命題を含む証明項があったら、その中でこの命題は二つの引数（一つは、数字\ ``n``\ 、もう一つは\ ``n``\ が偶数であることの根拠\ ``E``\ ）を持つ関数になっているはずです。しかし根拠となる\ ``E``\ は\ ``funny_prop1``\ の中では使われていませんから、これにわざわざ\ ``E``\ という名前をつけることはちょっと無意味です。このような場合は、次のように書くこともできます。

::

    Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

また、より親しみ深い記法では次のようにも書けます。

::

    Definition funny_prop1'' := forall n, ev n -> ev (n+4).

これはつまり "``P -> Q``\ " は単に "``forall (_:P), Q``\ "
の糖衣構文に過ぎないということを示しています。

論理積、連言（Conjunction、AND）
------------------------------

命題\ ``P``\ と\ ``Q``\ の論理積（\ ``logical conjunction``\ ）は、コンストラクタを一つしか持たない\ ``Inductive``\ を使った定義で表せます。

::

    Inductive and (P Q : Prop) : Prop :=
      conj : P -> Q -> (and P Q).

注意してほしいのは、前の章で取り上げた関数\ ``ev``\ の定義と同様に、この定義もパラメータ化された命題になっていますが、この場合はパラメータが数値ではなく命題である、ということです。

この定義の内容を直感的に理解するのに、そうややこしく考える必要はありません。\ ``and P Q``\ に根拠を与えるには、\ ``P``\ の根拠と\ ``Q``\ の根拠が必要だということです。もっと細かく言えば、

-  もし\ ``p``\ が\ ``P``\ の根拠で、\ ``q``\ が\ ``Q``\ の根拠であるなら、\ ``conj p q``\ は\ ``and P Q``\ の根拠となり得る。
-  これは\ ``and P Q``\ に根拠を与える唯一の方法である。というこは、もし\ ``and P Q``\ の根拠が得られたならば、\ ``p``\ を\ ``P``\ の根拠とし、\ ``q``\ を\ ``Q``\ の根拠とした上で\ ``conj p q``\ が得られるということです。

ここまでさんざん論理積（conjunction）という言葉を使ってきましたが、ここでもっと馴染みのある、中置の記法を導入することにしましょう。

::

    Notation "P /\ Q" := (and P Q) : type_scope.

（\ ``type_scope``\ という注釈は、Coqに対しこの記法が値にではなく、命題に現れるものであることを伝えまています。）

コンストラクタ\ ``conj``\ の型はどのようなものか考えてみましょう。

::

    Check conj.

conjが四つの引数（\ ``P``\ 、\ ``Q``\ という命題と、\ ``P``\ 、\ ``Q``\ の根拠）をとることに注目して下さい。

基本的なことから色々なことを組み立てていくエレガントさはさておき、このような方法でconjunctionを定義することの利点は、これを含む文を、既に知っているタクティックで証明できることです。例えば、もしゴールが論理積を含んでいる場合、このたった一つのコンストラクタ\ ``conj``\ を適用するだけで証明できます。それは、\ ``conj``\ の型を見ても分かるように現在のゴールを解決してからconjunctionの二つの部分を別々に証明するべきサブゴールにします。

::

    Theorem and_example :
      (ev 0) /\ (ev 4).
    Proof.
      apply conj.
       apply ev_0.
       apply ev_SS. apply ev_SS. apply ev_0.  Qed.

上の定理の証明オブジェクトをよく観察してみてください。

::

    Print and_example.

この型に注目してください。

::

        conj (ev 0) (ev 4) (... ev 0 の証明 ...) (... ev 4 の証明 ...)

さっき見た\ ``conj``\ と同じ形をしているのが分かるでしょう。

``apply conj``\ とするかわりに\ ``split``\ タクティックでも同じことができます。

::

    Theorem and_example' :
      (ev 0) /\ (ev 4).
    Proof.
      split.
        Case "left". apply ev_0.
        Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

逆に、\ ``inversion``\ タクティックを、コンテキストにある論理積の形をした仮定に使うことで、それの構築に使われた根拠を取り出し、コンテキストに加えることができます。

::

    Theorem proj1 : forall P Q : Prop,
      P /\ Q -> P.
    Proof.
      intros P Q H.
      inversion H as [HP HQ].
      apply HP.  Qed.

練習問題: ★, optional (proj2)
'''''''''''''''''''''''''''''

::

    Theorem proj2 : forall P Q : Prop,
      P /\ Q -> Q.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

::

    Theorem and_commut : forall P Q : Prop,
      P /\ Q -> Q /\ P.
    Proof.

      intros P Q H.
      inversion H as [HP HQ].
      split.
         apply HQ.
         apply HP.  Qed.

この定理の証明を理解しやすくするため、再び\ ``Case``\ タクティックについて話します。
この証明で起こっていることをよく観察すると、P and Q
の根拠となっている命題を抽出して、そこから逆向きに証明を再構築していることが分かるでしょう。

::

    Print and_commut.

練習問題: ★★ (and\_assoc)
'''''''''''''''''''''''''

次の証明では、\ ``inversion``\ が、入れ子構造になった命題\ ``H : P /\ (Q /\ R)``\ をどのように\ ``HP: P``,\ ``HQ : Q``,\ ``HR : R``\ に分解するか、という点に注意しなががら証明を完成させなさい。

::

    Theorem and_assoc : forall P Q R : Prop,
      P /\ (Q /\ R) -> (P /\ Q) /\ R.
    Proof.
      intros P Q R H.
      inversion H as [HP [HQ HR]].
    (* FILL IN HERE *) Admitted.

☐

練習問題: ★★, recommended (even\_ev)
''''''''''''''''''''''''''''''''''''

今度は、前の章で棚上げしていた\ ``even``\ と\ ``ev``\ の等価性をが別の方向から証明してみましょう。ここで左側のandは我々が実際に注目すべきものです。右のandは帰納法の仮定となって帰納法による証明に結びついていくことになるでしょう。なぜこれが必要となるかは、左側のandをそれ自身で証明しようとして、行き詰まってみるとかるでしょう。

::

    Theorem even_ev : forall n : nat,
      (even n -> ev n) /\ (even (S n) -> ev (S n)).
    Proof.

      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★
''''''''''''

次の命題の証明を示すオブジェクトを作成しなさい。

::

    Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
      (* FILL IN HERE *) admit.

☐

Iff （両含意）
~~~~~~~~~~~~

この、"if and only if（～である時、その時に限り）"
で表される「両含意」という論理は馴染みのあるもので、次の二つの「ならば（含意）」をandでつないだものです。

::

    Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

    Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity) : type_scope.

    Theorem iff_implies : forall P Q : Prop,
      (P <-> Q) -> P -> Q.
    Proof.
      intros P Q H.
      inversion H as [HAB HBA]. apply HAB.  Qed.

    Theorem iff_sym : forall P Q : Prop,
      (P <-> Q) -> (Q <-> P).
    Proof.

      intros P Q H.
      inversion H as [HAB HBA].
      split.
        Case "->". apply HBA.
        Case "<-". apply HAB.  Qed.

練習問題: ★ (iff\_properties)
'''''''''''''''''''''''''''''

上の、\ ``<->``\ が対称であることを示す証明 (``iff_sym``)
を使い、それが反射的であること、推移的であることを証明しなさい。

::

    Theorem iff_refl : forall P : Prop,
      P <-> P.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem iff_trans : forall P Q R : Prop,
      (P <-> Q) -> (Q <-> R) -> (P <-> R).
    Proof.
      (* FILL IN HERE *) Admitted.

ヒント: もしコンテキストに iff
を含む仮定があれば、\ ``inversion``\ を使ってそれを二つの含意の式に分割することができます。(なぜそうできるのか考えてみましょう。)

☐

練習問題: ★★ (MyProp\_iff\_ev)
''''''''''''''''''''''''''''''

ここまで、\ ``MyProp``\ や\ ``ev``\ が
これらの命題がある種の数値を特徴づける（偶数、などの）ことを見てきました。次の\ ``MyProp n <-> ev n``\ が任意の\ ``n``\ で成り立つことを証明しなさい。お遊びのつもりでかまわないので、その証明を、単純明快な証明、タクティックを使わないにような証明に書き換えてください。（ヒント：以前に使用した定理をうまく使えば、１行だけでかけるはずです！）

::

    Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
      (* FILL IN HERE *) admit.

☐

Coqのいくつかのタクティックは、証明の際に低レベルな操作を避けるため\ ``iff``\ を特別扱いします。
特に\ ``rewrite``\ を\ ``iff``\ に使うと、単なる等式以上のものとして扱ってくれます。

論理和、選言（Disjunction、OR）
-----------------------------

論理和（Disjunction、OR）も、帰納的な命題として定義できます。

::

    Inductive or (P Q : Prop) : Prop :=
      | or_introl : P -> or P Q
      | or_intror : Q -> or P Q.

    Notation "P \/ Q" := (or P Q) : type_scope.

コンストラクタ\ ``or_introl``\ の型が何か考えてください。

::

    Check or_introl.

このコンストラクタは三つの入力（\ ``P``\ 、\ ``Q``\ と名付けられた命題に加え、\ ``P``\ の根拠）を引数にとり、\ ``P /\ Q``\ の根拠を返します。次に、\ ``or_intror``\ の型を見てみましょう。

::

    Check or_intror.

ほとんど\ ``or_introl``\ と同じように見えますが、\ ``P``\ ではなく\ ``Q``\ の根拠が要求されています。

直観的には、命題\ ``P \/ Q``\ に根拠を与える方法は二つあることがわかります。

-  ``P``\ の根拠を与える。（そしてそれが\ ``P``\ の根拠であることを伝える。

これがコンストラクタ\ ``or_introl``\ の機能です）か、constructor), or

-  ``Q``\ の根拠をコンストラクタ\ ``or_intror``\ に与える。

``P \/ Q``\ は二つのコンストラクタを持っているので、\ ``P \/ Q``\ の形の仮定に\ ``inversion``\ を適用すると二つのサブゴールが生成されます。

::

    Theorem or_commut : forall P Q : Prop,
      P \/ Q  -> Q \/ P.
    Proof.
      intros P Q H.
      inversion H as [HP | HQ].
        Case "right". apply or_intror. apply HP.
        Case "left". apply or_introl. apply HQ.  Qed.

次のように、\ ``apply or_introl``\ 、\ ``apply or_intror``\ の代わりに\ ``left``\ 、\ ``right``\ という短縮版のタクティックを使うこともできます。

::

    Theorem or_commut' : forall P Q : Prop,
      P \/ Q  -> Q \/ P.
    Proof.
      intros P Q H.
      inversion H as [HP | HQ].
        Case "right". right. apply HP.
        Case "left". left. apply HQ.  Qed.

練習問題: ★★ optional (or\_commut'')
''''''''''''''''''''''''''''''''''''

``or_commut``\ の証明オブジェクトの型がどのようになるか、書き出してみてください。（ただし、定義済みの証明オブジェクトを\ ``Print``\ を使って見てみたりしないこと。）

::

    (* FILL IN HERE *)

☐

::

    Theorem or_distributes_over_and_1 : forall P Q R : Prop,
      P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
    Proof.
      intros P Q R. intros H. inversion H as [HP | [HQ HR]].
        Case "left". split.
          SCase "left". left. apply HP.
          SCase "right". left. apply HP.
        Case "right". split.
          SCase "left". right. apply HQ.
          SCase "right". right. apply HR.  Qed.

練習問題: ★★, recommended (or\_distributes\_over\_and\_2)
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem or_distributes_over_and_2 : forall P Q R : Prop,
      (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★ (or\_distributes\_over\_and)
''''''''''''''''''''''''''''''''''''''''

::

    Theorem or_distributes_over_and : forall P Q R : Prop,
      P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

``/\``\ 、\ ``\/``\ の\ ``andb``\ 、\ ``orb``\ への関連付け
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

我々はすでに、Coqの計算における型(``Type``) と論理の命題 (``Prop``)
との類似性について見てきました。ここではもう一つ、bool
型を扱う\ ``andb``\ と\ ``orb``\ が、\ ``/\``\ と\ ``\/``\ とのつながりともいうべきある種の類似性を持っていることに触れましょう。この類似性は、次の定理を見ればもっとはっきりします。これは、\ ``andb``\ や\ ``orb``\ が、ある入力に対する振る舞いを、その入力に対する命題にどのように変換するかを示したものです。

::

    Theorem andb_true__and : forall b c,
      andb b c = true -> b = true /\ c = true.
    Proof.

      intros b c H.
      destruct b.
        Case "b = true". destruct c.
          SCase "c = true". apply conj. reflexivity. reflexivity.
          SCase "c = false". inversion H.
        Case "b = false". inversion H.  Qed.

    Theorem and__andb_true : forall b c,
      b = true /\ c = true -> andb b c = true.
    Proof.

      intros b c H.
      inversion H.
      rewrite H0. rewrite H1. reflexivity. Qed.

練習問題: ★ (bool\_prop)
''''''''''''''''''''''''

::

    Theorem andb_false : forall b c,
      andb b c = false -> b = false \/ c = false.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem orb_true : forall b c,
      orb b c = true -> b = true \/ c = true.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem orb_false : forall b c,
      orb b c = false -> b = false /\ c = false.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

偽であるということ
------------------

論理学でいうところの「偽」は、Coqでは「帰納的に定義されてはいるがコンストラクタを一つも持たない命題」として定義されています。

::

    Inductive False : Prop := .

直観的な理解:``False``\ は、根拠を示す方法を一つも持たない命題

練習問題: ★ (False\_ind\_principle)
'''''''''''''''''''''''''''''''''''

「偽」に関する帰納的な公理を何か思いつくことができますか？

☐

``False``\ にはコンストラクタがないので、\ ``False``\ の意味するところのものを反転（invert）してもサブゴールが生成されません。このことはつまり、「偽」からはどんなゴールも証明できる、ということです。

::

    Theorem False_implies_nonsense :
      False -> 2 + 2 = 5.
    Proof.
      intros contra.
      inversion contra.  Qed.

これはどういうことでしょうか？\ ``inversion``\ タクティックは仮定\ ``contra``\ をその取りうるケースに分解し、それぞれにサブゴールを生成します。ここで\ ``contra``\ が\ ``False``\ の根拠となっているため、そこから取りうるケースは存在しません。このため、証明に値するサブゴールがなくなり、そこで証明が終わってしまうのです。

逆に、\ ``False``\ を証明する唯一の方法は、コンテキストに何か矛盾がないかを探すことです。

::

    Theorem nonsense_implies_False :
      2 + 2 = 5 -> False.
    Proof.
      intros contra.
      inversion contra.  Qed.

実際、\ ``False_implies_nonsense``\ の証明は、特定の意味を持つ証明すべきことを何も持っていないので、任意の\ ``P``\ に対して簡単に一般化できます。

::

    Theorem ex_falso_quodlibet : forall (P:Prop),
      False -> P.
    Proof.
      intros P contra.
      inversion contra.  Qed.

ラテン語の 「\ *ex falso quodlibet*
」は、文字通り「偽からはあなたの望むものすべてがもたらされる」というような意味です。この定理は、「
*principle of explosion* 」としても知られています。

真であるということ
~~~~~~~~~~~~~~~~~~

Coqで「偽」を定義することができたので、同じ考え方で「真」を定義することができるか、ということが次の関心事になります。もちろん、その答えは「Yes」です。

練習問題: ★★ (True\_induction)
''''''''''''''''''''''''''''''

``True``\ を、帰納的な命題として定義しなさい。あなたの定義に対してCoqはどのような帰納的原理を生成してくれるでしょうか。
（直観的には\ ``True``\ はただ当たり前のように根拠を示される命題であるべきです。代わりに、帰納的原理から帰納的な定義を逆にたどっていくほうが近道だと気づくかもしれません。）

::

    (* FILL IN HERE *)

☐

しかしながら、\ ``False``\ とは違い、広い意味で解釈すると\ ``True``\ には理論的な意味で奇妙なところがあります。ゴールの証明に使うには当たり前すぎ（それゆえつまらない）、仮定として有意義な情報を与えてくれないのです。

否定
----

命題\ ``P``\ の論理的な補集合というべきものは、\ ``not P``\ もしくは短縮形として\ ``~P``\ と表されます。

::

    Definition not (P:Prop) := P -> False.

直観的には
「もし\ ``P``\ がtrueでないなら、すべてが（\ ``False``\ でさえ）仮定\ ``P``\ から導かれるということです。.

::

    Notation "~ x" := (not x) : type_scope.

    Check not.

Coqで否定を扱えるようになるにはある程度慣れが必要です。たとえ何かがどう見ても真に思える場合でも、そのことをCoqに納得させるのは最初のうちはなかなか大変です。ウォームアップのつもりで、否定のに関する馴染みのある定理を取り上げてみましょう。

::

    Theorem not_False :
      ~ False.
    Proof.
      unfold not. intros H. inversion H.  Qed.

    Theorem contradiction_implies_anything : forall P Q : Prop,
      (P /\ ~P) -> Q.
    Proof.

      intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
      apply HNA in HP. inversion HP.  Qed.

    Theorem double_neg : forall P : Prop,
      P -> ~~P.
    Proof.

      intros P H. unfold not. intros G. apply G. apply H.  Qed.

練習問題: ★★, recommended (double\_neg\_inf)
''''''''''''''''''''''''''''''''''''''''''''

::

    []
    *)

FILL IN HERE ``double_neg``\ の非形式的な証明を書きなさい。:

*Theorem*:``P``\ implies\ ``~~P``, for any proposition\ ``P``.

*Proof*:(\* FILL IN HERE \*)☐

練習問題: ★★, recommended (contrapositive)
''''''''''''''''''''''''''''''''''''''''''

::

    Theorem contrapositive : forall P Q : Prop,
      (P -> Q) -> (~Q -> ~P).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★ (not\_both\_true\_and\_false)
'''''''''''''''''''''''''''''''''''''''''

::

    Theorem not_both_true_and_false : forall P : Prop,
      ~ (P /\ ~P).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

::

    Theorem five_not_even :
      ~ ev 5.
    Proof.

      unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
      inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

練習問題: ★ ev\_not\_ev\_S
''''''''''''''''''''''''''

定理\ ``five_not_even``\ は、「５は偶数ではない」というようなとても当たり前の事実を確認するものです。今度はもう少し面白い例です。

::

    Theorem ev_not_ev_S : forall n,
      ev n -> ~ ev (S n).
    Proof.
      unfold not. intros n H. induction H. 
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★ (informal\_not\_PNP)
''''''''''''''''''''''''''''''''

命題\ ``forall P : Prop, ~(P /\ ~P)``\ の形式的でない証明を（英語で）書きなさい。

::

    (* FILL IN HERE *)

☐

このうちいくつかは、古典論理ではtrueと判断できるにもかかわらず、Coqに組み込まれた機能だけでは証明できないものがあるので注意が必要です。

::

    Theorem classic_double_neg : forall P : Prop,
      ~~P -> P.
    Proof.

      intros P H. unfold not in H.


      Admitted.

練習問題: ★★★★★, optional (classical\_axioms)
'''''''''''''''''''''''''''''''''''''''''''''

さらなる挑戦を求める人のために、 Coq'Art book (p. 123)
から一つ練習問題を取り上げてみます。次の五つの文は、よく「古典論理の特性」と考えられているもの（Coqにビルトインされている構成的論理の対極にあるもの）です。これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、矛盾なく「証明されていない公理」として道具に加えることができます。これら五つの命題が等価であることを証明しなさい。

::

    Definition peirce := forall P Q: Prop,
      ((P->Q)->P)->P.
    Definition classic := forall P:Prop,
      ~~P -> P.
    Definition excluded_middle := forall P:Prop,
      P \/ ~P.
    Definition de_morgan_not_and_not := forall P Q:Prop,
      ~(~P/\~Q) -> P\/Q.
    Definition implies_to_or := forall P Q:Prop,
      (P->Q) -> (~P\/Q).

    (* FILL IN HERE *)

☐

不等であるということ
~~~~~~~~~~~~~~~~~~~~

``x <> y``\ というのは、\ ``~(x = y)``\ と同じことです。

::

    Notation "x <> y" := (~ (x = y)) : type_scope.

不等性は、その中に「否定」を含んでいるため、やはりその扱いにはある程度の慣れが必要です。ここで一つ有用なトリックをお見せしましょう。もし、証明すべきゴールがあり得ない式（例えば\ ``false = true``\ というような文）であった場合は、\ ``ex_falso_quodlibet``\ という補題をapplyで適用すると、ゴールを\ ``False``\ にすることができます。このことを覚えておけば、コンテキストの中の\ ``~P``\ という形の仮定を使うことがとても簡単になります。特に、\ ``x<>y``\ という形の仮定の場合はに有用です。

::

    Theorem not_false_then_true : forall b : bool,
      b <> false -> b = true.
    Proof.
      intros b H. destruct b.
      Case "b = true". reflexivity.
      Case "b = false".
        unfold not in H.
        apply ex_falso_quodlibet.
        apply H. reflexivity.   Qed.

練習問題: ★★, recommended (not\_eq\_beq\_false)
'''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem not_eq_beq_false : forall n n' : nat,
         n <> n' ->
         beq_nat n n' = false.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★, optional (beq\_false\_not\_eq)
''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem beq_false_not_eq : forall n m,
      false = beq_nat n m -> n <> m.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

存在量化子
----------

もう一つの論理的接続詞は、存在量化子（ *existentialquantification*
）です。これは、次のような定義でその意味をとらえることができます。

::

    Inductive ex (X:Type) (P : X->Prop) : Prop :=
      ex_intro : forall (witness:X), P witness -> ex X P.

この\ ``ex``\ は、型引数\ ``X``\ とそれに関する属性\ ``P``\ によって決まる命題です。「\ ``P``\ を満たす\ ``x``\ が存在する」という主張に根拠を与えるため、ある特定の値\ ``x``\ （「証拠」と呼ぶことにします）を具体的に示すことで\ ``P x``\ の根拠を得ることができます。つまりこれは、\ ``x``\ が性質\ ``P``\ を持っていることの根拠です。

例として、このような存在量化子を持つ命題を見てみましょう。:

::

    Definition some_nat_is_even : Prop :=
      ex nat ev.

この、命題を証明するためには、証拠として特定の値（この場合4）を与え、それが偶数である根拠を示す必要があります。

::

    Definition snie : some_nat_is_even :=
      ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Coqの容易な表記法の定義は、存在量化された命題を記述するための、より馴染みやすい表記を、ビルトインされたを全称量化子と同レベルで実現しています。そのおかげで、「偶数となる自然数が存在する」ことを示す命題を\ ``ex nat ev``\ と書く代わりに、たとえば\ ``exists x:nat, ev x``\ のように書くことができます。（これを理解するためにCoqの「表記法」がどのように作用しているかを完全に理解しないといけない、ということではありません。）

::

    Notation "'exists' x , p" := (ex _ (fun x => p))
      (at level 200, x ident, right associativity) : type_scope.
    Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
      (at level 200, x ident, right associativity) : type_scope.

存在を示す必要がある場合には、だいたいいつも同じようなタクティックの組み合わせが使われます。例えば、ある値の存在を証明する場合には、その値をコンストラクタ\ ``ex_intro``\ に\ ``apply``\ すればいいのです。\ ``ex_intro``\ の前提はその結論に現れないうような変数（これが「証拠」となります）を必要とするため、\ ``apply``\ を使用する際にはその値をきちんと提示することが必要になります。

::

    Example exists_example_1 : exists n, n + (n * n) = 6.
    Proof.
      apply ex_intro with (witness:=2).
      reflexivity.  Qed.

もう一度書きますが、ここでは具体的な値を証拠として用意する必要があります。

``apply ex_intro with (witness:=e)``\ と書く代わりに、短縮形として\ ``exists e``\ と記述することもできます。どちらも同じ意味です。

::

    Example exists_example_1' : exists n,
         n + (n * n) = 6.
    Proof.
      exists 2.
      reflexivity.  Qed.

逆に、コンテキストに置かれた仮定の中に存在を示すものがある場合は、それを\ ``inversion``\ タクティックで取り除くことができます。変数に名前を付けるため\ ``as...``\ パターンを使っていることに注目してください。Coqはそれを「証拠」につける名前とし、仮定が証拠を保持する根拠をそこから得ます。
（名前をきちんと選ばないと、Coqはそれを単なる証拠としか考えることができず、その先の証明で混乱してしまいます。）

::

    Theorem exists_example_2 : forall n,
         (exists m, n = 4 + m) ->
         (exists o, n = 2 + o).
    Proof.
      intros n H.
      inversion H as [m Hm].
      exists (2 + m).
      apply Hm.  Qed.

練習問題: ★ (english\_exists)
'''''''''''''''''''''''''''''

英語では、以下の命題は何を意味しているでしょうか？

::

          ex nat (fun n => ev (S n))

    (* FILL IN HERE *)

次の証明オブジェクトの定義を完成させなさい

::

    Definition p : ex nat (fun n => ev (S n)) :=
    (* FILL IN HERE *) admit.

☐

練習問題: ★ (dist\_not\_exists)
'''''''''''''''''''''''''''''''

"全ての\ ``x``\ について\ ``P``\ が成り立つ" ということと
"``P``\ を満たさない\ ``x``\ は存在しない"
ということが等価であることを証明しなさい。

::

    Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
      (forall x, P x) -> ~ (exists x, ~ P x).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★, optional (not\_exists\_dist)
'''''''''''''''''''''''''''''''''''''''''''

一方、古典論理の「排中律（law of the excluded
middle）」が必要とされる場合もあります。

::

    Theorem not_exists_dist :
      excluded_middle ->
      forall (X:Type) (P : X -> Prop),
        ~ (exists x, ~ P x) -> (forall x, P x).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★ (dist\_exists\_or)
'''''''''''''''''''''''''''''''

存在量化子が論理和において分配法則を満たすことを証明しなさい。

::

    Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
      (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
    Proof.
       (* FILL IN HERE *) Admitted.

☐

等しいということ（同値性）
------------------------

Coqには、等価という関係すら組み込まれていませんから、次のように帰納的に定義してやります（ここではこれまで散々使った標準ライブラリでの定義と衝突することを防ぐために、モジュールの中で定義することにします。）

::

    Module MyEquality.

    Inductive eq (X:Type) : X -> X -> Prop :=
      refl_equal : forall x, eq X x x.

次に定義するのは、標準的な中置記法です（Coqの型引数合成を使用しています）。

::

    Notation "x = y" := (eq _ x y)
                        (at level 70, no associativity) : type_scope.

この例は少し難解かもしれません。これがどういうものかを考えると、集合\ ``X``\ が与えられると、「集合\ ``X``\ に属する値
(``x``\ and\ ``y``)
にインデックスされた、\ ``x``\ は\ ``y``\ に等しい」というような命題の
*集団*
を定義してくれるということです。この集団に属する命題に根拠を与えるためには、一つの方法しかありません。それは、コンストラクタ\ ``refl_equal``\ に型\ ``X``\ とその値\ ``x : X``\ を適用し、\ ``x``\ が\ ``x``\ と等しいという根拠を生成することです。

次の定義は少し違った形になっています。 --
Coqの標準ライブラリではこちらの定義が採用されています。

::

    Inductive eq' (X:Type) (x:X) : X -> Prop :=
        refl_equal' : eq' X x x.

    Notation "x =' y" := (eq' _ x y)
                         (at level 70, no associativity) : type_scope.

練習問題: ★★★, optional (two\_defs\_of\_eq\_coincide)
'''''''''''''''''''''''''''''''''''''''''''''''''''''

これら二つの定義が等価であることを確認しなさい。

::

    Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
      x = y <-> x =' y.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

二つ目の定義の優れたところは、Coqが生成する帰納法の原理が正確に「ライプニッツの同値関係（
*Leibniz equality*
）」と親和している点です。それはつまり、「\ ``x``\ と\ ``y``\ が等しいということは、
任意の命題\ ``P``\ が\ ``x``\ でtrueとなるならば\ ``y``\ でもtrueとなる」ということです。

::

    Check eq'_ind.

一つ大事なことが残っています。確かに\ ``refl_equal``\ は\ ``2 = 2``\ というような証明に根拠を与えることに使えます。\ ``1 + 1 = 2``\ はどうでしょうか？答えは
Yes です。実際、これらは証明としてはほとんど同じようなものだと言えます。
その理由は Coq
が二つの式がシンプルな計算ルールによって交換可能であることをを示し、それを"同値である"として処理しているからです。このルールは\ ``Eval simpl``\ と同じものです。ただしこれには、関数適用の評価、定義のインライン化、\ ``match``\ の簡約が含まれています。

タクティックを使った同値性の証明では、\ ``simpl``\ を使うことで暗黙的にこの交換ルールに触れています（\ ``reflexivity``\ のような他のタクティックでも、明示的に、もしくは暗黙的に含まれています）。このことは、次のような明示的な証明オブジェクトで確認することができます。

::

    Definition four : 2 + 2 = 1 + 3 :=
      refl_equal nat 4.
    Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
      fun (X:Set) (x:X) => refl_equal (list X) [x].

    End MyEquality.

Inversion 再び
~~~~~~~~~~~~~~

これまでにも\ ``inversion``\ が等値性にからむ仮定や帰納的に定義された命題に対して使われるところを見てきました。今度もやることは変わりませんが、もう少し近くまで寄って\ ``inversion``\ の振る舞いを観察してみましょう。

一般的に\ ``inversion``\ タクティックは、

-  帰納的に定義された型\ ``P``\ の命題\ ``H``\ をとる。

-  その型\ ``P``\ の定義にある各コンストラクタ\ ``C``\ が、

   -  ``H``\ が\ ``C``\ から成っていると仮定するような新しいサブゴールを作る。
   -  ``C``\ の引数（前提）を、追加の仮定としてサブゴールのコンテキストに加える。
   -  ``C``\ の結論（戻り値の型）を現在のゴールとmatchして、\ ``C``\ を適用できるような一連の等式算出する。
   -  そしてこれらの等式をサブゴールのコンテキストに加えてから、
   -  もしこの等式が充足可能でない場合（\ ``S n = O``\ というような式を含むなど）は、
      即座にサブゴールを解決する。

例 :``or``\ で構築された仮定を反転（ invert
）すると、\ ``or``\ に二つのコンストラクタがあるため二つのサブゴールが生成されます。コンストラクタ
(``P \/ Q``)
の結果（戻り値の型）は\ ``P``\ や\ ``Q``\ の形からくる制約を付けません。そのため追加の等式がサブゴールのコンテキストに加えられることはありません。

例 :``and``\ で構築された仮定を反転（ invert
）すると、\ ``and``\ にはコンストラクタが一つしかないため、サブゴールも一つしか生成されません。やはり、コンストラクタ(``P /\ Q``)
の結果（戻り値の型）は\ ``P``\ や\ ``Q``\ の形からくる制約を付けず、追加の等式がサブゴールのコンテキストに加えられることはありません。このコンストラクタは引数を二つとりますが、それらはサブゴールのコンテキストに現れます。

例 :``eq``\ で構築された仮定を反転（ invert
）すると、これにもやはりコンストラクタが一つしかないため、サブゴールも一つしか生成されません。しかしこの場合コンストラクタ\ ``refl_equal``\ の形は我々にもう少し情報を与えてくれます。それは、\ ``eq``\ の二つの引数は同じでなければならないという点です。\ ``inversion``\ タクティックはこの事実をコンテキストに加えてくれます。

命題としての関係
----------------

``ev``\ のように数値でパラメータ化された命題は、属性（ *property*
）と見なすこともできます。つまり、それに属する値についてその命題が証明可能であるような\ ``nat``\ の部分集合の定義と見ることができるということです。同様に、引数（パラメータ）を二つ持つ命題は、その二つの「関係」を表していると考えられます。つまり、その命題について証明可能な値のペアの集合の定義、というわけです。

::

    Module LeFirstTry.

これまでにもすでに、帰納的に定義された関係の基本的なものは出てきていました。等値性がそれです。他にも、よく使われるものとして「等しいかまたは小さい」という関係があります。

この定義はかなり直観的なものになります。これは、ある数値がもう一つの数値より小さいかまたは等しい、ということを示すには二つの方法があることを示しています。一つはそれらが同じ数であるかどうかを確認すること。もう一つは最初の数が。二つ目の数の一つ前の数より小さいかまたは等しい、ということの根拠を得ることです。

::

    Inductive le : nat -> nat -> Prop :=
      | le_n : forall n, le n n
      | le_S : forall n m, (le n m) -> (le n (S m)).

    End LeFirstTry.

これはこれで\ ``<=``\ という関係の妥当なな定義だと言えます。しかし少し観察してみると定義の左側のに現れる\ ``n``\ は全て同じだということがわかります。ということは、個々のコンストラクタにではなく定義全体に全称量化子を使うことができるということです。このことは先程\ ``eq``\ という関係の二番目の定義でやったことと同じです。

::

    Inductive le (n:nat) : nat -> Prop :=
      | le_n : le n n
      | le_S : forall m, (le n m) -> (le n (S m)).

    Notation "m <= n" := (le m n).

少し対称性が損なわれたようにも見えますが、この二番目の定義の方がいいのです。なぜでしょうか？それは、こちらのほうがよりシンプルな帰納法の原理を生成してくれるからです（\ ``eq``\ の二番目の定義にも同じことが言えます）。

::

    Check le_ind.

一方、最初の定義に Coq
が生成する帰納法の原理には、もっと多くの量化子が含まれることになります。これでは、帰納法を使った証明がごちゃごちゃしてしまいます。これが\ ``le``\ の最初の定義で生成された帰納法の原理です。

コンストラクタ\ ``le_n``\ と\ ``le_S``\ を使った\ ``<=``\ にからむ証明は、前章の\ ``eq``\ がそうであったように、属性についての証明のいくつかのパターンに倣っています。\ ``<=``\ の形をしたゴール（例えば\ ``3<=3``\ や\ ``3<=6``\ など）に、そのコンストラクタをapply
することができますし、inversion
のようなタクティックを使って（\ ``~(2 <= 1)``\ の証明をしようとする際のように）
コンテキストに\ ``<=``\ を含む仮定から情報を抽出することもできます。

ここで、定義が正しくなされているのかのチェックをしてみましょう。（注意して欲しいのは、ここでやることが、最初のレクチャーで書いてもらった、ある種のシンプルな「ユニットテスト」のようなものですが、今回のものは以前のものとちょっと違います。今回のものには、\ ``simpl``\ や\ ``reflexivity``\ はほとんど役に立ちません。簡約だけで証明できるようなものではないからです。

::

    Theorem test_le1 :
      3 <= 3.
    Proof.

      apply le_n.  Qed.

    Theorem test_le2 :
      3 <= 6.
    Proof.

      apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

    Theorem test_le3 :
      ~ (2 <= 1).
    Proof.

      intros H. inversion H. inversion H1.  Qed.

「より小さい」という関係（\ ``n < m``\ ）は、\ ``le``\ を使って定義できます。

::

    Definition lt (n m:nat) := le (S n) m.

    Notation "m < n" := (lt m n).

他にも、数値の関係についていくつか見てみましょう。

::

    Inductive square_of : nat -> nat -> Prop :=
      sq : forall n:nat, square_of n (n * n).

    Inductive next_nat (n:nat) : nat -> Prop :=
      | nn : next_nat n (S n).

    Inductive next_even (n:nat) : nat -> Prop :=
      | ne_1 : ev (S n) -> next_even n (S n)
      | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

練習問題: ★★, recommended (total\_relation)
'''''''''''''''''''''''''''''''''''''''''''

二つの自然数のペア同士の間に成り立つ帰納的な関係\ ``total_relation``\ を定義しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: ★★ (empty\_relation)
''''''''''''''''''''''''''''''

自然数の間では決して成り立たない関係\ ``empty_relation``\ を帰納的に定義しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: ★★★, recommended (R\_provability)
'''''''''''''''''''''''''''''''''''''''''''

::

    Module R.

次は三つや四つの値の間に成り立つ関係を同じように定義してみましょう。例えば、次のような数値の三項関係が考えられます。

::

    Inductive R : nat -> nat -> nat -> Prop :=
       | c1 : R 0 0 0
       | c2 : forall m n o, R m n o -> R (S m) n (S o)
       | c3 : forall m n o, R m n o -> R m (S n) (S o)
       | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
       | c5 : forall m n o, R m n o -> R n m o.


    []
    *)

FILL IN HERE

-  次の命題のうち、この関係を満たすと証明できると言えるのはどれでしょうか。
   -``R 1 1 2``

   -  ``R 2 2 6``
   -  この関係\ ``R``\ の定義からコンストラクタ\ ``c5``\ を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。
   -  この関係\ ``R``\ の定義からコンストラクタ\ ``c4``\ を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。

(\* FILL IN HERE \*)☐

練習問題: ★★★, optional (R\_fact)
'''''''''''''''''''''''''''''''''

関係\ ``R``\ の、等値性に関する特性をあげ、それを証明しなさい。
それは、もし\ ``R m n o``\ が true
なら\ ``m``\ についてどんなことが言えるでしょうか？\ ``n``\ や\ ``o``\ についてはどうでしょうか？その逆は？

::

    (* FILL IN HERE *)

☐

::

    End R.

練習問題: ★★★, recommended (all\_forallb)
'''''''''''''''''''''''''''''''''''''''''

リストに関する属性\ ``all``\ を定義しなさい。それは、型\ ``X``\ と属性\ ``P : X -> Prop``\ をパラメータとし、\ ``all X P l``\ が「リスト\ ``l``\ の全ての要素が属性
[P} を満たす」とするものです。

::

    Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
      (* FILL IN HERE *)
    .

``Poly.v``\ の練習問題\ ``forall_exists_challenge``\ に出てきた関数\ ``forallb``\ を思い出してみましょう。

::

    Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
      match l with
        | [] => true
        | x :: l' => andb (test x) (forallb test l')
      end.

属性\ ``all``\ を使って関数\ ``forallb``\ の仕様を書き、それを満たすことを証明しなさい。できるだけその仕様が厳格になるようにすること。

関数\ ``forallb``\ の重要な性質が、あなたの仕様から洩れている、ということはありませんか？

::

    (* FILL IN HERE *)

☐

練習問題: ★★★★, optional (filter\_challenge)
''''''''''''''''''''''''''''''''''''''''''''

Coq
の主な目的の一つは、プログラムが特定の仕様を満たしていることを証明することです。それがどういうことか、\ ``filter``\ 関数の定義が仕様を満たすか証明してみましょう。まず、その関数の仕様を非形式的に書き出してみます。

集合\ ``X``\ と関数\ ``test: X->bool``\ 、リスト\ ``l``\ とその型\ ``list X``\ を想定する。さらに、\ ``l``\ が二つのリスト\ ``l1``\ と\ ``l2``\ が順序を維持したままマージされたもので、リスト\ ``l1``\ の要素はすべて\ ``test``\ を満たし、\ ``l2``\ の要素はすべて満たさないとすると、\ ``filter test l = l1``\ が成り立つ。

リスト\ ``l``\ が\ ``l1``\ と\ ``l2``\ を順序を維持したままマージしたものである、とは、それが\ ``l1``\ と\ ``l2``\ の要素をすべて含んでいて、しかも
互いに入り組んではいても\ ``l1``\ 、\ ``l2``\ の要素が同じ順序になっている、ということです。例えば、

::

        [1,4,6,2,3]

は、以下の二つを順序を維持したままマージしたものです。

::

        [1,6,2]

と、

::

        [4,3]

課題は、この仕様をCoq
の定理の形に書き直し、それを証明することです。（ヒント：まず、一つのりすとが二つのリストをマージしたものとなっている、ということを示す定義を書く必要がありますが、これは帰納的な関係であって、\ ``Fixpoint``\ で書くようなものではありません。）

::

    (* FILL IN HERE *)

☐

練習問題: ★★★★★, optional (filter\_challenge\_2)
''''''''''''''''''''''''''''''''''''''''''''''''

``filter``\ の振る舞いに関する特性を別の切り口で表すとこうなります。「\ ``test``\ の結果が\ ``true``\ なる要素だけでできた、リスト\ ``l``\ のすべての部分リストの中で、\ ``filter test l``\ が最も長いリストである。」これを形式的に記述し、それを証明しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: ★★★★, optional (no\_repeats)
''''''''''''''''''''''''''''''''''''''

次の、帰納的に定義された命題を見て、

::

    Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
      | ai_here : forall l, appears_in a (a::l)
      | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

値\ ``a``\ が、少なくとも一度はリスト\ ``l``\ の中に現れるということを、厳密に表現する方法を考えなさい。

``appears_in``\ に関するウォームアップ問題としてもう一つ、

::

    Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X),
         appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
    Proof.
      (* FILL IN HERE *) Admitted.

    Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X),
         appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
    Proof.
      (* FILL IN HERE *) Admitted.

では、\ ``appears_in``\ を使って命題\ ``disjoint X l1 l2``\ を定義してください。これは、型\ ``X``\ の二つのリスト\ ``l1``\ 、\ ``l2``\ が共通の要素を持たない場合にのみ証明可能な命題です。

::

    (* FILL IN HERE *)

次は、\ ``appears_in``\ を使って帰納的な命題\ ``no_repeats X l``\ を定義してください。これは,
型\ ``X``\ のリスト\ ``l``\ の中のどの要素も、他の要素と異なっている場合のみ証明できるような命題です。例えば、\ ``no_repeats nat [1,2,3,4``]
や\ ``no_repeats bool [``]
は証明可能ですが、\ ``no_repeats nat [1,2,1``]
や\ ``no_repeats bool [true,true``] は証明できないようなものです。

::

    (* FILL IN HERE *)

最後に、\ ``disjoint``\ 、\ ``no_repeats``\ 、\ ``++``\ （リストの結合）の三つを使った、何か面白い定理を考えて、それを証明してください。

::

    (* FILL IN HERE *)

☐

少し脱線:``<=``\ と\ ``<``\ についてのさらなる事実
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

ここで少し新しいことを中断して、\ ``<=``\ や\ ``<``\ といった関係についての事実をいくつか書き溜めていくことにしましょう。それらはここから先に進む際に必要になってくるばかりでなく、その証明自体がとてもよい練習問題になってくれます。

練習問題: ★★, optional (le\_exercises)
''''''''''''''''''''''''''''''''''''''

::

    Theorem O_le_n : forall n,
      0 <= n.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem n_le_m__Sn_le_Sm : forall n m,
      n <= m -> S n <= S m.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem Sn_le_Sm__n_le_m : forall n m,
      S n <= S m -> n <= m.
    Proof.
      intros n m.  generalize dependent n.  induction m.
      (* FILL IN HERE *) Admitted.

    Theorem le_plus_l : forall a b,
      a <= a + b.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem plus_lt : forall n1 n2 m,
      n1 + n2 < m ->
      n1 < m /\ n2 < m.
    Proof.
     (* FILL IN HERE *) Admitted.

    Theorem lt_S : forall n m,
      n < m ->
      n < S m.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem ble_nat_true : forall n m,
      ble_nat n m = true -> n <= m.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem ble_nat_n_Sn_false : forall n m,
      ble_nat n (S m) = false ->
      ble_nat n m = false.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem ble_nat_false : forall n m,
      ble_nat n m = false -> ~(n <= m).
    Proof.

      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★, recommended (nostutter)
''''''''''''''''''''''''''''''''''''''

述語の帰納的な定義を定式化できるようになるというのは、これから先の学習に必要なスキルになってきます。

この練習問題は、何の力も借りず自力で解いてください。もし誰かの力を借りてしまった場合は、そのことをコメントに書いておいてください。

同じ数値が連続して現れるリストを "stutters"
（どもったリスト）と呼ぶことにします。述語 "``nostutter mylist``\ "
は、\ ``mylist``\ が「どもったリスト」でないことを意味しています。\ ``nostutter``\ の帰納的な定義を記述しなさい。（これは以前の練習問題に出てきた\ ``no_repeats``\ という述語とは異なるものです。リスト\ ``1,4,1``\ は
repeats ではありますが stutter ではありません。）

::

    Inductive nostutter:  list nat -> Prop :=
     (* FILL IN HERE *)
    .

できた定義が、以下のテストを通過することを確認してください。通過できないものがあったら、定義を修正してもかまいません。あなたの書いた定義が、正しくはあるけれど私の用意した模範解答と異なっているかもしれません。その場合、このテストを通過するために別の証明を用意する必要があります。

以下の Example
にコメントとして提示された証明には、色々な種類の\ ``nostutter``\ の定義に対応できるようにするため、まだ説明していないタクティックがいくつか使用されています。
まずこれらのコメントをはずしただけの状態で確認できればいいのですが、もしそうしたいなら、これらの証明をもっと基本的なタクティックで書き換えて証明してもかまいません。

::

    Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
    (* FILL IN HERE *) Admitted.


    Example test_nostutter_2:  nostutter [].
    (* FILL IN HERE *) Admitted.


    Example test_nostutter_3:  nostutter [5].
    (* FILL IN HERE *) Admitted.


    Example test_nostutter_4:      not (nostutter [3,1,1,4]).
    (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★★, optional (pigeonhole principle)
'''''''''''''''''''''''''''''''''''''''''''''''

「鳩の巣定理（ "pigeonhole principle"
）」は、「数えるあげる」ということについての基本的な事実を提示しています。「もし\ ``n``\ 個の鳩の巣に\ ``n``\ 個より多い数のものを入れようとするなら、どのような入れ方をしてもいくつかの鳩の巣には必ず一つ以上のものが入ることになる。」というもので、この、数値に関する見るからに自明な事実を証明するにも、なかなか自明とは言えない手段が必要になります。我々は既にそれを知っているのですが...

まず、補題を二つほど証明しておきます。（既に数値のリストについては証明済みのものですが、任意のリストについてはのものはまだないので）

::

    Lemma app_length : forall {X:Type} (l1 l2 : list X),
      length (l1 ++ l2) = length l1 + length l2.
    Proof.
      (* FILL IN HERE *) Admitted.

    Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
      appears_in x l ->
      exists l1, exists l2, l = l1 ++ (x::l2).
    Proof.
      (* FILL IN HERE *) Admitted.

そして、述語\ ``repeats``\ の定義をします（以前の練習問題\ ``no_repeats``\ に類似したものです）。それは\ ``repeats X l``\ が、「\ ``l``\ の中に少なくとも一組の同じ要素（型\ ``X``\ の）を含む」という主張となるようなものです。

::

    Inductive repeats {X:Type} : list X -> Prop :=
      (* FILL IN HERE *)
    .

この「鳩の巣定理」を定式化する方法を一つ挙げておきましょう。リスト\ ``l2``\ が鳩の巣に貼られたラベルの一覧を、リスト\ ``l1``\ はそのラベルの、アイテムへの割り当ての一覧を表しているとします。もしラベルよりも沢山のアイテムがあったならば、少なくとも二つのアイテムに同じラベルが貼られていることになります。おそらくこの証明には「排中律（\ ``excluded_middle``\ ）」が必要になるでしょう。

::

    Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
      excluded_middle ->
      (forall x, appears_in x l1 -> appears_in x l2) ->
      length l2 < length l1 ->
      repeats l1.
    Proof.  intros X l1. induction l1.
      (* FILL IN HERE *) Admitted.

☐

選択課題
--------

``/\``\ や\ ``\/``\ のための帰納法の原理
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

論理積（連言）や論理和（連言）に関する帰納法の原理は、帰納的に定義された命題に対して簡約された帰納法の原理を
Coq
が生成する方法をとてもよく示しています。これについては最後の章でお話しします。とりあえずこれに挑戦してみてください。

練習問題: ★ (and\_ind\_principle)
'''''''''''''''''''''''''''''''''

連言（ conjunction ）についての帰納法の原理を予想して、確認しなさい。

☐

練習問題: ★ (or\_ind\_principle)
''''''''''''''''''''''''''''''''

選言（ disjunction ）についての帰納法の原理を予想して、確認しなさい。

☐

::

    Check and_ind.

命題\ ``and P Q``\ の帰納的な定義から、

::

         Inductive and (P Q : Prop) : Prop :=
           conj : P -> Q -> (and P Q).

我々は Coq がこのような帰納法の原理を生成することを期待します。

::

         and_ind_max :
           forall (P Q : Prop) (P0 : P /\ Q -> Prop),
                (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
                forall a : P /\ Q, P0 a

しかし実際には、もっとシンプルで使いやすいものが生成されます。

::

         and_ind :
           forall P Q P0 : Prop,
                (P -> Q -> P0) ->
                P /\ Q -> P0

同様に、\ ``or P Q``\ の帰納的な定義が与えられると、

::

         Inductive or (P Q : Prop) : Prop :=
           | or_introl : P -> or P Q
           | or_intror : Q -> or P Q.

以下のような、原則通りの帰納法の原理を制する代わりに、

::

         or_ind_max :
           forall (P Q : Prop) (P0 : P \/ Q -> Prop),
                (forall a : P, P0 (or_introl P Q a)) ->
                (forall b : Q, P0 (or_intror P Q b)) ->
                forall o : P \/ Q, P0 o

Coq はこのような帰納法の原理が生成されます。

::

         or_ind :
           forall P Q P0 : Prop,
                (P -> P0) ->
                (Q -> P0) ->
                P \/ Q -> P0

帰納法のための明白な証明オブジェクト
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

タクティックを使った証明は一般に簡単に済むことが多いですが、証明式を直接書いてしまえるなら、そうしたほうが簡単な場合もあります。特に、Coq
にちょっとだけ変わった方法をとらせたい時はそうです。

``nat``\ の帰納的な定義からCoqが自動的に生成した自然数に関する帰納法の原理を思い出してください。

この帰納法についての補題には何のタネも仕掛けもありません。これは単に、証明を必要とする
Coq の別の補題です。Coq はこれにも自動的に証明を生成してくれます。

::

    Print nat_ind.  Print nat_rect.

これは次のように読めます :``P``\ が 0
の場合に成り立つという根拠\ ``f``\ と\ ``forall n:nat, P n -> P (S n)``\ の根拠\ ``f0``\ があると仮定します。そうすると、\ ``P``\ が任意の自然数\ ``n``\ で成り立つことを、再帰的に定義された関数\ ``F``\ （ここでは、トップレベルで使われる\ ``Fixpoint``\ ではなく、\ ``Fix``\ を使って定義されています）を使って示すことができます。\ ``F``\ は\ ``n``\ について以下のようなパターンマッチをしています：

-  もし 0
   ならば、\ ``F``\ は\ ``f``\ を\ ``P n``\ が成り立つことの根拠とする。
-  もし\ ``S n0``\ ならば、\ ``F``\ は\ ``P n0``\ が成り立つ根拠を手に入れるために、\ ``n0``\ を持ってそれ自身を再帰呼び出しする。そうして得た根拠が\ ``f0``\ に適用され\ ``P (S n)``\ が成り立つことが示される。

``F``\ は、集合\ ``Set``\ ではなく、根拠\ ``Prop``\ を操作することになっただけの普通の再帰的な関数です。

関数型プログラミングが少し面白くなるような脇道です。もしかするとあなたは関数\ ``F``\ の\ ``match``\ が、アノテーション\ ``as n0 return (P n0)``\ を必要としていることに気づいたかもしれません。それは
Coq
の型チェッカが二つの\ ``match``\ の枝が、実は同じ型\ ``P n``\ を返すことを明確にするために必要なものなのですが、これは本質的に
Haskell の GADT (generalized algebraic datatype)
と同じものです。実際、\ ``F``\ は依存型（ *dependent* type
）をしており、その結果の方はその引数に依存します。 GADT
はこのような単純な依存型を表現する際に使えます。我々は、\ ``nat_ind``\ の証明に使用したこのようなアプローチを、標準的でない（
*non-standard*
）帰納法の原理を証明する際にも使うことができます。以前このような証明をしようとしていたことを思い出してください。\ ``forall n : nat, even n -> ev n``.

これを、通常の\ ``n``\ に対する帰納法でやろうとしても失敗してしまいます。なぜなら、この帰納法の原理は\ ``even n -> even (S n)``\ を証明しようとする時にしかうまく機能してくれないからです。これはもちろん証明不能な命題です。このような場合、前の章ではちょっとした小技を使いました。

[Theorem even\_ev : forall n : nat,(even n -> ev n) / (even (S n) -> ev
(S n))].

これについては、標準的でない帰納法の原理（二つずつ、となるような）を定義して証明することで、より良い証明が得られます。

::

    Definition nat_ind2 :
        forall (P : nat -> Prop),
        P 0 ->
        P 1 ->
        (forall n : nat, P n -> P (S(S n))) ->
        forall n : nat , P n :=
           fun P => fun P0 => fun P1 => fun PSS =>
              fix f (n:nat) := match n return P n with
                                 0 => P0
                               | 1 => P1
                               | S (S n') => PSS n' (f n')
                              end.

一度これを手にいれてしまえば、今回のような帰納法の原理を使った証明全般にこれを使うことができます。これを補題としてタクティックを使うと、さらに直観に反したものになります（試してみてください！）。\ ``induction ... using``\ タクティックは、このように標準的でない帰納法の原理を取る際に便利です。

::

    Lemma even_ev' : forall n, even n -> ev n.
    Proof.
     intros.
     induction n as [ | |n'] using nat_ind2.
      Case "even 0".
        apply ev_0.
      Case "even 1".
        inversion H.
      Case "even (S(S n'))".
        apply ev_SS.
        apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H.
    Qed.

Coq の信頼できるコンピューティング基盤
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

ここで一つの疑問が起こってきます。自動化された証明アシスタントが「なぜ信用できるのか？」という疑問です。つまり、これらの実装にバグがあるなら、その証明にも疑いを持たざるを得ません。

このような考えを完全に排除することはできませんが、Coq
カリー・ハワード同型対応をその基礎に置いているという事実は Coq
自身の強い基礎ともなっています。なぜなら、命題は型であり、証明は項であり、まだ証明されていない命題が妥当かどうかを調べることは、項の型をチェックする（
*type-checking*
）ことに等しいからです。型チェッカは十分に信頼できるほど小さく率直に書かれたプログラムであり、それこそが
Coq
の「信頼できるコンピューティング基盤」となっています。その「信頼性が必要となる一部のコード」は正確に動き、また十分に小さいのです。型チェッカの役割とはなんでしょうか？その一番の役割は、各々の関数の適用で、予想された型と実際の型が一致していることを確認することです。つまり、\ ``match``\ の各枝の式が、帰納的な型のコンストラクタと対応しており、すべてが同じ型を返すようになっているか、などです。しかしこれには若干の弱点もあります。

-  Coq
   の型はそれ自身が式となっているため、その型チェッカがそれらを比較する前際に、変換ルールに基づいて正規化しなければならない。
-  型チェッカは、\ ``match``\ の式が「尽くされている（\ *exhaustive*
   ）ことを確認しなければならない。つまり、その型ににあるコンストラクタに対応する枝をすべて持っていなければならい。その理由は、次に提示された証明オブジェクトについて考えればわかるはずです。

   ::

         Definition or_bogus : forall P Q, P \/ Q -> P :=
           fun (P Q : Prop) (A : P \/ Q) =>
              match A with
              | or_introl H => H
              end.

この定義では、型は正しく一致していますが、\ ``match``\ が\ ``or``\ の一方のコンストラクタのことしか考えていません。Coq
は、このようなケースがないかをチェックし、このような定義を拒絶します。

-  型チェッカは、各\ ``fix``\ の式が終了することを確認しなければならない。これは文法レベルで「各々の再帰呼び出しに元々の引数にわたってきた式の部分式が渡されていること」をチェックをすることで実現されている。この理由の本質的なところを理解するために次の証明について考えてください。

   ::

             Definition nat_false : forall (n:nat), False :=
                fix f (n:nat) : False := f n.

やはり、これも型について何も問題はありませんが、残念なことに Coq
はこの定義を拒絶します。

Coq
の「確実さ」は、タクティックの仕組みではなく、型チェックの仕組みによってもたらされていることに注目してください。もしタクティックの実装にバグがあれば（実際にこれはあったことです！）、タクティックは間違った証明を構築してしまうでしょう。しかし、\ ``Qed``\ を入力した時点で、Coq
はその正しさを１から検証しなおします。型チェッカを通過した補題のみ、その後の証明の構築に使える定理となることができるのです。
