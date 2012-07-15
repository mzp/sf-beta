UseTactics\_J:Coq用タクティックライブラリのご紹介
=================================================

Coqはビルトインのタクティックの集合を持っています。\ ``reflexivity``\ 、\ ``intros``\ 、\ ``inversion``\ などです。これらのタクティックだけで証明を構成することは可能ですが、より強力なタクティックの集合を使うことで、生産性を飛躍的に上げることができます。この章では、とても便利なのに、いろいろな理由でデフォルトのCoqでは用意されていないたくさんのタクティックを説明します。それらのタクティックは、\ ``LibTactics_J.v``\ ファイルに定義されています。

::

    Require Import LibTactics_J.

注記: SSReflect
は強力なタクティックを提供する別のパッケージです。ライブラリ"LibTactics"は"SSReflect"と次の2点で異なります:

-  "SSReflect"は主として数学の定理を証明するために開発されました。
   一方、"LibTactics"は主としてプログラミング言語の定理の証明のために開発されました。特に"LibTactics"は、"SSReflect"パッケージには対応するものがない、いくつもの有用なタクティックを提供します。
-  "SSReflect"はタクティックの提示方法を根底から考え直しています。
   一方、"LibTactics"はCoqタクティックの伝統的提示方法をほとんど崩していません。このことからおそらく"LibTactics"の方が"SSReflect"よりとっつきやすいと思われます。

この章は"LibTactics"ライブラリの最も便利な機能に焦点を当てたチュートリアルです。"LibTactics"のすべての機能を示すことを狙ってはいません。タクティックの完全なドキュメンテーションはソースファイル\ ``LibTactics_J.v``\ にあります。さらに、タクティックのはたらきを見せるデモは、ファイル\ ``LibTacticsDemos_J.v``\ にあります。(訳注:原文ファイル群にも
LibTacticsDemos.v
は含まれていません。このファイル名でネット検索してみてください。)

タクティックの説明にはほとんど、「ソフトウェアの基礎」("Software
Foundations")のコースの主要な章から抽出した例を使います。タクティックのいろいろな使い方を説明するために、ゴールを複製するタクティックを使います。より詳しく言うと、\ ``dup``\ は現在のゴールを2つにコピーします。また\ ``dup n``\ はゴールのn個のコピーを作ります。

導入と場合分けについてのタクティック
------------------------------------

この節では、以下のタクティックを説明します:

-  ``introv``:仮定に名前をつける時間を省くのに使います
-  ``inverts``:``inversion``\ タクティックの改良です
-  ``cases``:情報を失わずに場合分けします
-  ``cases_if``:``if``\ の引数について自動的に場合分けします

タクティック\ ``introv``
~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module IntrovExamples.
      Require Import Stlc_J.
      Import Imp_J STLC.

タクティック\ ``introv``\ は、定理の変数を自動的に導入し、生成される仮定に明示的に名前を付けます。次の例では、決定性の主張に関する変数\ ``c``\ 、\ ``st``\ 、\ ``st1``\ 、\ ``st2``\ には明示的に命名する必要はありません。これらは補題の主張の中で既に名前が付けられているからです。これに対して、2つの仮定\ ``E1``\ と\ ``E2``\ には名前をつけると便利です。

::

    Theorem ceval_deterministic: forall c st st1 st2,
      c / st || st1 ->
      c / st || st2 ->
      st1 = st2.
    Proof.
      introv E1 E2.

仮定に名前をつける必要がない場合には、引数なしで\ ``introv``\ を呼ぶことができます。

::

    Theorem ceval_and_ceval_step_coincide: forall c st st',
          c / st || st'
      <-> exists i, ceval_step st c i = Some st'.
    Proof.
      introv.

タクティック\ ``introv``\ は\ ``forall``\ と\ ``->``\ が交互に現れる主張にも適用できます。

::

    Theorem ceval_deterministic': forall c st st1,
      (c / st || st1) -> forall st2, (c / st || st2) -> st1 = st2.
    Proof.
      introv E1 E2.

``intros``\ と同様、\ ``introv``\ も、構造化パターンを引数にとることができます。

::

    Theorem ceval_step__ceval: forall c st st',
          (exists i, ceval_step st c i = Some st') ->
          c / st || st'.
    Proof.
      introv [i E].

注記:
タクティック\ ``introv``\ は、定義をunfoldしないと仮定が出てこない場合にも使うことができます。

::

    End IntrovExamples.

タクティック\ ``inverts``
~~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module InvertsExamples.
      Require Import Stlc_J Equiv_J Imp_J.
      Import STLC.

Coqの\ ``inversion``\ タクティックは3つの点で十分なものだと言えません。1つ目は、\ ``inversion``\ は、\ ``subst``\ で置換して消してしまいたいような、たくさんの等式を生成することです。2つ目は、仮定に意味のない名前を付けることです。3つ目は、\ ``inversion H``\ は、ほとんどの場合\ ``H``\ を後で使うことはないにもかかわらず、コンテキストから\ ``H``\ を消去しないことです。タクティック\ ``inverts``\ はこの3つの問題すべてを扱います。このタクティックは、タクティック\ ``inversion``\ にとって代わることを意図したものです。

次の例は、タクティック\ ``inverts H``\ が、置換を適切に行う以外は\ ``inversion H``\ と同様にはたらくことを示しています。

::

    Theorem skip_left: forall c,
      cequiv (SKIP; c) c.
    Proof.
      introv. split; intros H.
      dup.

次にもう少し興味深い例を見てみましょう。

::

    Theorem ceval_deterministic: forall c st st1 st2,
      c / st || st1  ->
      c / st || st2 ->
      st1 = st2.
    Proof.
      introv E1 E2. generalize dependent st2.
      (ceval_cases (induction E1) Case); intros st2 E2.
      admit. admit.

タクティック\ ``inverts H as.``\ は\ ``inverts H``\ と同様ですが、次の点が違います。\ ``inverts H as.``\ では、生成される変数と仮定がコンテキストではなくゴールに置かれます。この戦略により、これらの変数と仮定に\ ``intros``\ や\ ``introv``\ を使って明示的に名前を付けることができるようになります。

::

    Theorem ceval_deterministic': forall c st st1 st2,
         c / st || st1  ->
         c / st || st2 ->
         st1 = st2.
    Proof.
      introv E1 E2. generalize dependent st2.
      (ceval_cases (induction E1) Case); intros st2 E2;
        inverts E2 as.
      Case "E_Skip". reflexivity.
      Case "E_Ass".

``inversion``\ を使ったとするとゴールが1つだけできる場合に、\ ``inverts``\ を\ ``inverts H as H1 H2 H3``\ の形で呼ぶことができます。このとき新しい仮定は\ ``H1``\ 、\ ``H2``\ 、\ ``H3``\ と名付けられます。言い換えると、タクティック\ ``inverts H as H1 H2 H3``\ は、\ ``invert H; introv H1 H2 H3``\ と同じです。例を示します。

::

    Theorem skip_left': forall c,
      cequiv (SKIP; c) c.
    Proof.
      introv. split; intros H.
      inverts H as U V.

より複雑な例です。特に、invertされた仮定の名前を再利用できることを示しています。

::

    Example typing_nonexample_1 :
      ~ exists T,
          has_type empty
            (tm_abs a ty_Bool
                (tm_abs b ty_Bool
                   (tm_app (tm_var a) (tm_var b))))
            T.
    Proof.
      dup 3.

注意:
稀に、仮定\ ``H``\ をinvertするときに\ ``H``\ をコンテキストから除去したくない場合があります。その場合には、タクティック\ ``inverts keep H``\ を使うことができます。キーワード\ ``keep``\ は仮定をコンテキストに残せということを示しています。

タクティック\ ``cases``\ と\ ``cases_if``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module CasesExample.
      Require Import Stlc_J.
      Import STLC.

タクティック\ ``cases E``\ は、\ ``remember E as x; destruct x``\ の略記法です。しかしそれだけでなく、\ ``remember``\ が生成する等式の右辺と左辺を逆にしたものを生成します。例えば、\ ``cases``\ は、等式\ ``true = beq_id k1 k2``\ ではなく等式\ ``beq_id k1 k2 = true``\ を作ります。なぜなら、\ ``true = beq_id k1 k2``\ は読むのにかなり不自然な形だからです。タクティック\ ``cases E as H``\ の形にすると、生成された等式に名前を付けることができます。

注記:``cases``\ は\ ``case_eq``\ にかなり近いです。\ ``remember``\ および\ ``case_eq``\ との互換性のために、ライブラリ"LibTactics"には\ ``cases'``\ というタクティックが用意されています。\ ``cases'``\ は\ ``remember``\ および\ ``case_eq``\ とまったく同じ等式を生成します。つまり、\ ``beq_id k1 k2 = true``\ ではなく\ ``true = beq_id k1 k2``\ という形の等式です。次の例は、タクティック\ ``cases' E as H``\ の振る舞いを表しています。

::

    Theorem update_same : forall x1 k1 k2 (f : state),
      f k1 = x1 ->
      (update f k1 x1) k2 = f k2.
    Proof.
      intros x1 k1 k2 f Heq.
      unfold update. subst.
      dup.

タクティック\ ``cases_if``\ はゴールまたはコンテキストの\ ``if``\ の引数として現れる式\ ``E``\ に対して\ ``cases E``\ を呼びます。このため、タクティック\ ``cases_if``\ を使うと、ゴールに既に現れている式をコピーする必要がなくなります。先と同様、互換性のため、ライブラリには\ ``cases_if'``\ というタクティックが用意されています。また\ ``cases_if' as H``\ という形で、生成される等式に名前をつけることができます。

::

    Theorem update_same' : forall x1 k1 k2 (f : state),
      f k1 = x1 ->
      (update f k1 x1) k2 = f k2.
    Proof.
      intros x1 k1 k2 f Heq.
      unfold update. subst.

n-引数論理演算のためのタクティック
----------------------------------

Coqは and と or
を2引数コンストラクタ\ ``/\``\ および\ ``\/``\ でコード化するため、\ ``N``\ 個の事実についての
and や or の扱いがとても面倒なものになります。このため、"LibTactics"では
n個の and と or
を直接サポートするタクティックを提供します。さらに、n個の存在限量に対する直接的サポートも提供します。

この節では以下のタクティックを説明します:

-  ``splits``:n個の and を分解します
-  ``branch``:n個の or を分解します
-  ``exists``:n個の存在限量の証明をします。

   Module NaryExamples. Require Import References\_J SfLib\_J. Import
   STLCRef.

タクティック\ ``splits``
~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``splits``\ は、\ ``n``\ 個の命題の and
に適用され、\ ``n``\ 個のサブゴールを作ります。例えば、ゴール\ ``G1 /\ G2 /\ G3``\ を3つのサブゴール\ ``G1``\ 、\ ``G2``\ 、\ ``G3``\ に分解します。

::

    Lemma demo_splits : forall n m,
      n > 0 /\ n < m /\ m < n+10 /\ m <> 3.
    Proof.
      intros. splits.
    Admitted.

タクティック\ ``branch``
~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``branch k``\ は n個の or
の証明に使うことができます。例えば、ゴールが\ ``G1 \/ G2 \/ G3``\ という形のとき、タクティック\ ``branch 2``\ は\ ``G2``\ だけをサブゴールとします。次の例は\ ``branch``\ タクティックの振る舞いを表しています。

::

    Lemma demo_branch : forall n m,
      n < m \/ n = m \/ m < n.
    Proof.
      intros.
      destruct (lt_eq_lt_dec n m) as [[H1|H2]|H3].
      branch 1. apply H1.
      branch 2. apply H2.
      branch 3. apply H3.
    Qed.

タクティック\ ``exists``
~~~~~~~~~~~~~~~~~~~~~~~~

ライブラリ "LibTactics" は
n個の存在限量についての記法を用意しています。例えば、\ ``exists x, exists y, exists z, H``\ と書く代わりに\ ``exists x y z, H``\ と書くことができます。同様に、ライブラリはn引数のタクティック\ ``exists a b c``\ を提供します。これは、\ ``exists a; exists b; exists c``\ の略記法です。次の例はn個の存在限量についての記法とタクティックを表しています。

::

    Theorem progress : forall ST t T st,
      has_type empty ST t T ->
      store_well_typed ST st ->
      value t \/ exists t' st', t / st ==> t' / st'.

注記:
n個の存在限量についての同様の機能が標準ライブラリのモジュール\ ``Coq.Program.Syntax``\ で提供されています。ただ、このモジュールのものは限量対象が4つまでしか対応していませんが、\ ``LibTactics``\ は10個までサポートしています。

::

    End NaryExamples.

等式を扱うタクティック
----------------------

他の対話的証明支援器と比べたCoqの大きな弱点の一つは、等式に関する推論のサポートが比較的貧弱なことです。次に説明するタクティックは、等式を扱う証明記述を簡単にすることを狙ったものです。

この節で説明するタクティックは次のものです:

-  ``asserts_rewrite``: 書き換えのための等式を導入します
-  ``cuts_rewrite``: サブゴールが交換される以外は同じです
-  ``substs``:``subst``\ タクティックを改良します
-  ``fequals``:``f_equal``\ タクティックを改良します
-  ``applys_eq``:
   仮定\ ``P x z``\ を使って、等式\ ``y = z``\ を自動生成し、\ ``P x y``\ を証明します

   Module EqualityExamples.

タクティック\ ``asserts_rewrite``\ と\ ``cuts_rewrite``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``asserts_rewrite (E1 = E2)``\ はゴール内の\ ``E1``\ を\ ``E2``\ で置換し、ゴール\ ``E1 = E2``\ を生成します。

::

    Theorem mult_0_plus : forall n m : nat,
      (0 + n) * m = n * m.
    Proof.
      dup.

注記:``asserts_rewrite (E1 = E2) in H``\ と書いた場合、
-------------------------------------------------------

ゴールの代わりに仮定\ ``H``\ を書き換えます。

タクティック\ ``cuts_rewrite (E1 = E2)``\ は\ ``asserts_rewrite (E1 = E2)``\ と同様ですが、等式\ ``E1 = E2``\ が最初のサブゴールになります。

::

    Theorem mult_0_plus' : forall n m : nat,
      (0 + n) * m = n * m.
    Proof.
      intros n m.
      cuts_rewrite (0 + n = n).
        reflexivity.

より一般には、タクティック\ ``asserts_rewrite``\ と\ ``cuts_rewrite``\ は補題を引数としてとることができます。例えば\ ``asserts_rewrite (forall a b, a*(S b) = a*b+a)``\ と書くことができます。この記法は\ ``a``\ や\ ``b``\ が大きな項であるとき便利です。その大きな項を繰り返さずに済むからです。

::

    Theorem mult_0_plus'' : forall u v w x y z: nat,
      (u + v) * (S (w * x + y)) = z.
    Proof.
      intros. asserts_rewrite (forall a b, a*(S b) = a*b+a).

タクティック\ ``substs``
~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``substs``\ は\ ``subst``\ と同様ですが、\ ``subst``\ と違い、ゴールが\ ``x = f x``\ のような「循環する等式」を含むときも失敗しません。

::

    Lemma demo_substs : forall x y (f:nat->nat),
      x = f x -> y = x -> y = f x.
    Proof.
      intros. substs.

タクティック\ ``fequals``
~~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``fequals``\ は\ ``f_equal``\ と同様ですが、生成される自明なサブゴールを直接解決してしまう点が違います。さらに、タクティック\ ``fequals``\ はタプル間の等式の扱いが強化されています。

::

    Lemma demo_fequals : forall (a b c d e : nat) (f : nat->nat->nat->nat->nat),
      a = 1 -> b = e -> e = 2 ->
      f a b c d = f 1 2 c 4.
    Proof.
      intros. fequals.

タクティック\ ``applys_eq``
~~~~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``applys_eq``\ は\ ``eapply``\ の変種で、単一化できない部分項間の等式を導入します。例えば、ゴールが命題\ ``P x y``\ で、\ ``P x z``\ が成立するという仮定\ ``H``\ があるとします。また\ ``y``\ と\ ``z``\ が等しいことが証明できることはわかっているとします。すると、タクティック\ ``assert_rewrite (y = z)``\ を呼び、ゴールを\ ``P x z``\ に変えることができます。しかしこれには、\ ``y``\ と\ ``z``\ の値のコピー&ペーストが必要になります。タクティック\ ``applys_eq``\ を使うと、この場合\ ``applys_eq H 1``\ とできます。すると、ゴールは証明され、サブゴール\ ``y = z``\ が残ります。\ ``applys_eq``\ の引数の値\ ``1``\ は、\ ``P x y``\ の右から1番目の引数についての等式を導入したいことを表します。以下の3つの例は、それぞれ\ ``applys_eq H 1``\ 、\ ``applys_eq H 2``\ 、\ ``applys_eq H 1 2``\ を呼んだときの振る舞いを示します。

::

    Axiom big_expression_using : nat->nat.

もしミスマッチが\ ``P``\ の第2引数ではなく第1引数だった場合には、\ ``applys_eq H 2``\ と書きます。出現は右からカウントされることを思い出してください。

::

    Lemma demo_applys_eq_2 : forall (P:nat->nat->Prop) x y z,
      P (big_expression_using z) x ->
      P (big_expression_using y) x.
    Proof.
      introv H. applys_eq H 2.
    Admitted.

2つの引数にミスマッチがある場合、2つの等式が欲しくなります。そのためには、\ ``applys_eq H 1 2``\ とできます。より一般に、タクティック\ ``applys_eq``\ は1つの補題と自然数の列を引数としてとります。

::

    Lemma demo_applys_eq_3 : forall (P:nat->nat->Prop) x1 x2 y1 y2,
      P (big_expression_using x2) (big_expression_using y2) ->
      P (big_expression_using x1) (big_expression_using y1).
    Proof.
      introv H. applys_eq H 1 2.

便利な略記法をいくつか
----------------------

チュートリアルのこの節では、証明記述をより短かく、より読みやすくするのに役立つタクティックをいくつか紹介します:

-  ``unfolds``\ (引数なし): 先頭の定義を unfold します
-  ``false``: ゴールを\ ``False``\ で置換します
-  ``gen``:``dependent generalize``\ の略記法です
-  ``skip``: サブゴールをスキップします(存在変数と組み合わせて使います)
-  ``sort``: 証明コンテキストの下の命題を動かします

タクティック\ ``unfolds``
~~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module UnfoldsExample.
      Require Import Hoare_J.

タクティック\ ``unfolds``\ (引数なし) はゴールの先頭の定数を unfold
します。このタクティックは定数を明示的に指名する手間を省きます。

::

    Lemma bexp_eval_true : forall b st,
      beval st b = true -> (bassn b) st.
    Proof.
      intros b st Hbe. dup.

注記:
タクティック\ ``hnf``\ はすべての先頭の定数をunfoldしますが、これと対照的に\ ``unfolds``\ は1つだけunfoldします。

注記:
タクティック\ ``unfolds in H``\ は仮定\ ``H``\ の先頭の定義をunfoldします。

::

    End UnfoldsExample.

タクティック\ ``false``\ と\ ``tryfalse``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``false``\ は任意のゴールを\ ``False``\ に置換します。簡単に言うと、\ ``apply ex_falso_quodlibet``\ の略記法です。さらに\ ``false``\ は、不条理な仮定(``False``\ や\ ``0 = S n``\ など)や矛盾した仮定(``x = true``\ と\ ``x = false``\ など)を含むゴールを証明します。

::

    Lemma demo_false :
      forall n, S n = 1 -> n = 0.
    Proof.
      intros. destruct n. reflexivity. false.
    Qed.

タクティック\ ``tryfalse``\ は\ ``try solve [false``]
の略記法です。このタクティックはゴールの矛盾を探します。タクティック\ ``tryfalse``\ は一般に場合分けの後で呼ばれます。

::

    Lemma demo_tryfalse :
      forall n, S n = 1 -> n = 0.
    Proof.
      intros. destruct n; tryfalse. reflexivity.
    Qed.

タクティック\ ``gen``
~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``gen``\ は\ ``generalize dependent``\ の略記法です。たくさんの引数を一度に受けます。このタクティックは\ ``gen x y z``\ という形で呼びます。

::

    Module GenExample.
      Require Import Stlc_J.
      Import STLC.

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S ->
         has_type empty v U ->
         has_type Gamma (subst v x t) S.
    Proof.
      dup.

タクティック\ ``skip``\ 、\ ``skip_rewrite``\ 、\ ``skip_goal``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

サブゴールをadmitできることは証明を構成するうえでとても便利です。証明の一番興味深いケースに最初にフォーカスできるようになるからです。タクティック\ ``skip``\ は\ ``admit``\ と似ていますが、証明が存在変数を含む場合にも機能します。存在変数とは、\ ``?24``\ のように名前がクエスチョンマークから始まる変数で、典型的には\ ``eapply``\ によって導入されるものであったことを思い出してください。

::

    Module SkipExample.
      Require Import Stlc_J.
      Import STLC.

    Example astep_example1 :
      (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ==>a* (ANum 15).
    Proof.
      eapply rsc_step. skip.

タクティック\ ``skip H: P``\ は仮定\ ``H: P``\ をコンテキストに追加します。このときに命題\ ``P``\ が真かどうかのチェックはしません。このタクティックは、事実を、証明を後回しにして利用するのに便利です。注意:``skip H: P``\ は単に\ ``assert (H:P). skip.``\ の略記法です。

::

    Theorem demo_skipH : True.
    Proof.
      skip H: (forall n m : nat, (0 + n) * m = n * m).
    Admitted.

タクティック\ ``skip_rewrite (E1 = E2)``\ はゴールの\ ``E1``\ を\ ``E2``\ で置換します。このときに\ ``E1``\ が実際に\ ``E2``\ と等しいかはチェックしません。

::

    Theorem mult_0_plus : forall n m : nat,
      (0 + n) * m = n * m.
    Proof.
      dup.

注記:
タクティック\ ``skip_rewrite``\ は実際は\ ``asserts_rewrite``\ と同じように補題を引数としてとることができます。

タクティック\ ``skip_goal``\ は現在のゴールを仮定として追加します。このごまかしは帰納法による証明の構造の構成の際に、帰納法の仮定がより小さい引数だけに適用されるかを心配しないで済むため有用です。\ ``skip_goal``\ を使うことで、証明を次の2ステップで構成できます：最初に、帰納法の仮定の細部の調整に時間を浪費せずに、主要な議論が通るかをチェックし、その後、帰納法の仮定の呼び出しの調整にフォーカスするというステップです。

::

    Theorem ceval_deterministic: forall c st st1 st2,
      c / st || st1 ->
      c / st || st2 ->
      st1 = st2.
    Proof.

タクティック\ ``sort``
~~~~~~~~~~~~~~~~~~~~~~

::

    Module SortExamples.
      Require Import Imp_J.

タクティック\ ``sort``\ は証明コンテキストを再構成し、変数が上に仮定が下になるようにします。これにより、証明コンテキストはより読みやすくなります。

::

    Theorem ceval_deterministic: forall c st st1 st2,
      c / st || st1 ->
      c / st || st2 ->
      st1 = st2.
    Proof.
      intros c st st1 st2 E1 E2.
      generalize dependent st2.
      (ceval_cases (induction E1) Case); intros st2 E2; inverts E2.
      admit. admit.

高度な補題具体化のためのタクティック
------------------------------------

この最後の節では、補題に引数のいくつかを与え、他の引数は明示化しないままで、補題を具体化するメカニズムについて記述します。具体値を与えられない変数は存在変数となり、具体化が与えられない事実はサブゴールになります。

注記:
この具体化メカニズムは「暗黙の引数」メカニズムをはるかに超越する能力を提供します。この節で記述する具体化メカニズムのポイントは、どれだけの
'\_'記号を書かなければならないかの計算に時間を使わなくてよくなることです。

この節では、Coq
の便利な連言(and)と存在限量の分解機構を使います。簡単に言うと、\ ``intros``\ や\ ``destruct``\ は\ ``[H1 [H2 [H3 [H4 H5``]]]]の略記法としてパターン\ ``(H1 & H2 & H3 & H4 & H5)``\ をとることができます。例えば\ ``destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub``].]は\ ``destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).``\ と書くことができます。

``lets``\ のはたらき
~~~~~~~~~~~~~~~~~~~~

利用したい補題(または仮定)がある場合、大抵、この補題に明示的に引数を与える必要があります。例えば次のような形です:``destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).``\ 何回も'\_'記号を書かなければならないのは面倒です。何回書くかを計算しなければならないだけでなく、このことで証明記述がかなり汚なくもなります。タクティック\ ``lets``\ を使うことで、次のように簡単に書くことができます:``lets (T & Hctx & Hsub): typing_inversion_var Htypt.``

簡単に言うと、このタクティック\ ``lets``\ は補題のたくさんの変数や仮定を特定します。記法は\ ``lets I: E0 E1 .. EN``\ という形です。そうすると事実\ ``E0``\ に引数\ ``E1``\ から\ ``EN``\ を与えて\ ``I``\ という名前の仮定を作ります。すべての引数を与えなければならないわけではありませんが、与えなければならない引数は、正しい順番で与えなければなりません。このタクティックは、与えられた引数を使って補題をどうしたら具体化できるかを計算するために、型の上の
first-match アルゴリズムを使います。

::

    Module ExamplesLets.
      Require Import Subtyping_J.

最初に、型が\ ``has_type G (tm_var x) T``\ である仮定\ ``H``\ を持つとします。タクティック\ ``lets K: typing_inversion_var H``\ を呼ぶことで補題\ ``typing_inversion_var``\ を結論として得ることができます。以下の通りです。

::

    Lemma demo_lets_1 : forall (G:context) (x:id) (T:ty),
      has_type G (tm_var x) T -> True.
    Proof.
      intros G x T H. dup.

今、\ ``G``\ 、\ ``x``\ 、\ ``T``\ の値を知っていて、\ ``S``\ を得たいとします。また、サブゴールとして\ ``has_type G (tm_var x) T``\ が生成されていたとします。\ ``typing_inversion_var``\ の残った引数のすべてをサブゴールとして生成したいことを示すために、'\_'を三連した記号\ ``___``\ を使います。(後に、\ ``___``\ を書くのを避けるために\ ``forwards``\ という略記用タクティックを導入します。)

::

    Lemma demo_lets_2 : forall (G:context) (x:id) (T:ty), True.
    Proof.
      intros G x T.
      lets (S & Eq & Sub): typing_inversion_var G x T ___.
    Admitted.

通常、\ ``has_type G (tm_var x) T``\ を証明するのに適したコンテキスト\ ``G``\ と型\ ``T``\ は1つだけしかないので、実は\ ``G``\ と\ ``T``\ を明示的に与えることに煩わされる必要はありません。\ ``lets (S & Eq & Sub): typing_inversion_var x``\ とすれば十分です。このとき、変数\ ``G``\ と\ ``T``\ は存在変数を使って具体化されます。

::

    Lemma demo_lets_3 : forall (x:id), True.
    Proof.
      intros x.
      lets (S & Eq & Sub): typing_inversion_var x ___.
    Admitted.

より極端に、\ ``typing_inversion_var``\ の具体化のために引数をまったく与えないこともできます。この場合、3つの単一化変数が導入されます。

::

    Lemma demo_lets_4 : True.
    Proof.
      lets (S & Eq & Sub): typing_inversion_var ___.
    Admitted.

注意:``lets``\ に補題の名前だけを引数として与えた場合、その補題が証明コンテキストに追加されるだけで、その引数を具体化しようとすることは行いません。

::

    Lemma demo_lets_5 : True.
    Proof.
      lets H: typing_inversion_var.
    Admitted.

``lets``\ の最後の便利な機能は '\_'
を2つ続けた記号\ ``__``\ です。これを使うと、いくつかの引数が同じ型を持つとき引数を1つスキップできます。以下の例は、\ ``m``\ を値\ ``3``\ に具体化したい一方、\ ``n``\ は存在変数を使って具体化したい場面です。

::

    Lemma demo_lets_underscore :
      (forall n m, n <= m -> n < m+1) -> True.
    Proof.
      intros H.

注意:
証明記述の中で\ ``H``\ の名前を言う必要がないとき、\ ``lets H: E0 E1 E2``\ の代わりに\ ``lets: E0 E1 E2``\ と書くことができます。

注意:
タクティック\ ``lets``\ は5つまでの引数をとることができます。5個を越える引数を与えることができる場合に、別の構文があります。キーワード\ ``>>``\ から始まるリストを使ったものです。例えば\ ``lets H: (>> E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 10)``\ と書きます。

::

    End ExamplesLets.

``applys``\ 、\ ``forwards``\ 、\ ``specializes``\ のはたらき
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

タクティック\ ``applys``\ 、\ ``forwards``\ 、\ ``specializes``\ は\ ``lets``\ を特定の用途に使う場面での略記法です。

-  ``forwards``\ は補題のすべての引数を具体化する略記法です。
   より詳しくは、\ ``forwards H: E0 E1 E2 E3``\ は\ ``lets H: E0 E1 E2 E3 ___``\ と同じです。ここで\ ``___``\ の意味は前に説明した通りです。
-  ``applys``\ は、\ ``lets``\ の高度な具体化モードにより補題を構築し、
   それをすぐに使うことにあたります。これから、\ ``applys E0 E1 E2 E3``\ は、\ ``lets H: E0 E1 E2 E3``\ の後\ ``eapply H``\ 、\ ``clear H``\ と続けることと同じです。
-  ``specializes``\ は、コンテキストの仮定を特定の引数でその場で具体化することの略記法です。
   より詳しくは、\ ``specializes H E0 E1``\ は\ ``lets H': H E0 E1``\ の後\ ``clear H``\ 、\ ``rename H' into H``\ と続けることと同じです。

``applys``\ の使用例は以下で出てきます。\ ``specializes``\ と\ ``forwards``\ の使用例は、チュートリアルファイル\ ``UseAuto_J.v``\ にいくつか含まれています。

具体化の例
~~~~~~~~~~

::

    Module ExamplesInstantiations.
      Require Import Subtyping_J.

以下の証明では、いくつかの場所で\ ``lets``\ が\ ``destruct``\ の代わりに、\ ``applys``\ が\ ``apply``\ の代わりに使われます。その場所は
"old:"で始まるコメントで示されています。\ ``lets``\ を使う練習問題も示されています。

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S ->
         has_type empty v U ->
         has_type Gamma (subst v x t) S.
    Proof with eauto.
      intros Gamma x U v t S Htypt Htypv.
      generalize dependent S. generalize dependent Gamma.
      (tm_cases (induction t) Case); intros; simpl.
      Case "tm_var".
        rename i into y.


        (* old: destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].*) 


           (* old: destruct (free_in_context _ _ S empty Hcontra) as [T' HT']... *) 


        (* 練習問題: 次の[destruct]を[lets]に換えなさい *)


        (* old: destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
                eapply T_App... *)


        (* old: destruct (typing_inversion_abs _ _ _ _ _ Htypt). *)


        (* old: apply T_Sub with (ty_arrow T1 T2)... *)


        (* old: assert (subtype ty_Unit S) by apply (typing_inversion_unit _ _ Htypt)... *)

    lets: typing_inversion_unit Htypt...


    Qed.

    End ExamplesInstantiations.

