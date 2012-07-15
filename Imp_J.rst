Imp\_J: 単純な命令型プログラム
==============================

この章では、コースの残りに続く新しい方向へ進み始めます。ここまではもっぱらCoq自身について学習してきましたが、ここからは、主として別のものを形式化するためにCoqを使います。はじめの例は、Imp
と呼ばれる単純な命令型プログラミング言語です。下の例は、おなじみの数学的関数を
Imp で書いたものです。

::

         Z ::= X;
         Y ::= 1;
         WHILE not (Z = 0) DO
           Y ::= Y * Z;
           Z ::= Z - 1
         END

この章ではImpの構文(*syntax*)と意味(*semantics*)をどのように定義するかを見ます。続く章では、プログラムの同値性(*program
equivalence*)の理論を展開し、命令型プログラムについての推論のための論理として一番知られているホーア論理(*Hoare
Logic*)を紹介します。

Sflib
^^^^^

マイナーな技術的ポイント:
ここまでの定義を\ ``Logic_J.v``\ からインポートする代わりに、\ ``Sflib_J.v``\ という小さなライブラリをインポートします。このライブラリは、前の章の定義や定理のうち、残りの章で実際に使うものだけを集めたものです。読者はそれほど違うものとは感じないでしょう。というのは、Sflib
で抜けているもののほとんどは、Coqの標準ライブラリの定義と同じものだからです。こうする主な理由は、Coqのグローバルな環境を整理して、例えば、関係する定理を探すのを容易にするためです。

::

    Require Export SfLib_J.

算術式とブール式
----------------

Impを三つの部分に分けて示します: 最初に算術式(*arithmetic
expressions*)とブール式(*boolean
expressions*)、次にこれらの式に変数(*variables*)を加えたもの、そして最後に代入(assignment)、条件分岐(conditions)、コマンド合成(sequencing)、ループ(loops)を持つコマンド(*commands*)の言語です。

::

    Module AExp.

構文
~~~~

次の2つの定義は、算術式とブール式の抽象構文(*abstract
syntax*)を定めます。

::

    Inductive aexp : Type :=
      | ANum : nat -> aexp
      | APlus : aexp -> aexp -> aexp
      | AMinus : aexp -> aexp -> aexp
      | AMult : aexp -> aexp -> aexp.

    Inductive bexp : Type :=
      | BTrue : bexp
      | BFalse : bexp
      | BEq : aexp -> aexp -> bexp
      | BLe : aexp -> aexp -> bexp
      | BNot : bexp -> bexp
      | BAnd : bexp -> bexp -> bexp.

この章では、プログラマが実際に書く具象構文から抽象構文木への変換は省略します。例えば、文字列\ ``"1+2*3"``\ をAST(Abstract
Syntax Tree,
抽象構文木)\ ``APlus (ANum 1) (AMult (ANum 2) (ANum 3))``\ にする変換のことです。この変換ができる字句解析器と構文解析器をファイル\ ``ImpParser_J.v``\ で簡単に実装します。このファイル(``Imp_J.v``)を理解するには\ ``ImpParser_J.v``\ の理解は必要ではありませんが、もしそれらの技術についてのコース(例えばコンパイラコース)を受講していないならば、ざっと見てみるのも良いでしょう。

比較のため、同じ抽象構文を定義する慣習的なBNF(Backus-Naur
Form)文法を以下に示します:

::

        aexp ::= nat
               | aexp '+' aexp
               | aexp '-' aexp
               | aexp '*' aexp

        bexp ::= true
               | false
               | aexp '=' aexp
               | aexp '<=' aexp
               | bexp 'and' bexp
               | 'not' bexp

上述のCoq版と比較して...

-  BNFはより非形式的です。例えば、
   BNFは式の表面的な構文についていくらかの情報を与えています(可算は\ ``+``\ と記述され、それは中置記号であるという事実などです)が、字句解析と構文解析の他の面は定めないままになっています(``+``\ 、\ ``-``\ 、\ ``*``\ の相対的優先順位などです)。(例えばコンパイラを実装するときに)この記述を形式的定義にするためには、追加の情報、および人間の知性が必要でしょう。
   Coq版はこれらの情報を整合的に省略し、抽象構文だけに集中します。

-  一方、BNF版はより軽くて、おそらく読むのがより簡単です。
   非形式的であることで柔軟性を持っているので、黒板を使って議論する場面などでは特段に有効です。そういう場面では、細部をいちいち正確に確定させていくことより、全体的アイデアを伝えることが重要だからです。
   実際、BNFのような記法は山ほどあり、人は皆、それらの間を自由に行き来しますし、通常はそれらのうちのどのBNFを使っているかを気にしません。その必要がないからです。おおざっぱな非形式的な理解だけが必要なのです。

両方の記法に通じているのは良いことです。非形式的なものは人間とのコミュニケーションのために、形式的なものは実装と証明のためにです。

評価
~~~~

算術式を評価する(*evaluating*)とその式を1つの数に簡約します。

::

    Fixpoint aeval (e : aexp) : nat :=
      match e with
      | ANum n => n
      | APlus a1 a2 => (aeval a1) + (aeval a2)
      | AMinus a1 a2  => (aeval a1) - (aeval a2)
      | AMult a1 a2 => (aeval a1) * (aeval a2)
      end.

    Example test_aeval1:
      aeval (APlus (ANum 2) (ANum 2)) = 4.
    Proof. reflexivity. Qed.

同様に、ブール式を評価するとブール値になります。

::

    Fixpoint beval (e : bexp) : bool :=
      match e with
      | BTrue       => true
      | BFalse      => false
      | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
      | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
      | BNot b1     => negb (beval b1)
      | BAnd b1 b2  => andb (beval b1) (beval b2)
      end.

最適化(Optimization)
~~~~~~~~~~~~~~~~~~~~

ここまで定義したものはわずかですが、その定義から既にいくらかのものを得ることができます。算術式をとって、それを少し簡単化する関数を定義するとします。すべての\ ``0+e``\ (つまり\ ``(APlus (ANum 0) e)``)を単に\ ``e``\ にするものです。

::

    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.

この最適化が正しいことをすることを確認するために、いくつかの例についてテストして出力がよさそうかを見てみることができます。

::

    Example test_optimize_0plus:
      optimize_0plus (APlus (ANum 2)
                            (APlus (ANum 0)
                                   (APlus (ANum 0) (ANum 1))))
      = APlus (ANum 2) (ANum 1).
    Proof. reflexivity. Qed.

しかし、もし最適化が正しいことを確認したいならば、

-  

   -  つまり、最適化した式がオリジナルの式と同じ評価結果を返すことを確認したいならば、

証明すべきです。

::

    Theorem optimize_0plus_sound: forall e,
      aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e. induction e.
      Case "ANum". reflexivity.
      Case "APlus". destruct e1.
        SCase "e1 = ANum n". destruct n.
          SSCase "n = 0".  simpl. apply IHe2.
          SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
        SCase "e1 = APlus e1_1 e1_2".
          simpl. simpl in IHe1. rewrite IHe1.
          rewrite IHe2. reflexivity.
        SCase "e1 = AMinus e1_1 e1_2".
          simpl. simpl in IHe1. rewrite IHe1.
          rewrite IHe2. reflexivity.
        SCase "e1 = AMult e1_1 e1_2".
          simpl. simpl in IHe1. rewrite IHe1.
          rewrite IHe2. reflexivity.
      Case "AMinus".
        simpl. rewrite IHe1. rewrite IHe2. reflexivity.
      Case "AMult".
        simpl. rewrite IHe1. rewrite IHe2. reflexivity.  Qed.

Coq の自動化
------------

前の証明の最後の繰り返しはちょっと面倒です。今のところまだ耐えられますが、証明対象の言語や算術式や最適化が今に比べて著しく複雑だったら、現実的に問題になるでしょう。

ここまで、Coq
のタクティックのほんのひとつかみだけですべての証明をしてきていて、証明を自動的に構成する非常に強力な機構を完全に無視してきました。このセクションではこれらの機構のいくつかを紹介します。それ以上のものを、以降のいくつかの章で次第に見ることになるでしょう。それらに慣れるには多少エネルギーが必要でしょう。

-  

   -  Coq の自動化は電動工具です。--

しかし自動化機構を使うことで、より複雑な定義や、より興味深い性質について、退屈で繰り返しの多いローレベルな詳細に飲み込まれることなく、作業をスケールアップできます。

タクティカル(Tacticals)
~~~~~~~~~~~~~~~~~~~~~~~

タクティカル(*tactical*)は Coq
の用語で、他のタクティックを引数に取るタクティックのことです。「高階タクティック」("higher-order
tactics")と言っても良いでしょう。

``try``\ タクティカル
^^^^^^^^^^^^^^^^^^^^^

非常にシンプルなタクティカルの1つが\ ``try``\ です。\ ``T``\ がタクティックのとき、タクティック\ ``try T``\ は\ ``T``\ と同様ですが、\ ``T``\ が失敗するとき\ ``try T``\ は(失敗せずに)何もしない点が違います。

``;``\ タクティカル
^^^^^^^^^^^^^^^^^^^

別の非常に基本的なタクティカルは\ ``;``\ と書かれます。\ ``T``,\ ``T1``,
...,\ ``Tn``\ がタクティックのとき、

::

          T; [T1 | T2 | ... | Tn]

はタクティックで、最初に\ ``T``\ を行ない、\ ``T``\ によって生成された最初のサブゴールに\ ``T1``\ を行ない、二番目のサブゴールに\ ``T2``\ を行ない、...
という処理をします。

すべての\ ``Ti``\ が同じタクティック\ ``T'``\ であるという特別な場合、

::

          T; [T' | T' | ... | T']

と書く代わりに\ ``T;T'``\ と書くだけで済ますことができます。つまり、\ ``T``\ と\ ``T'``\ がタクティックのとき、\ ``T;T'``\ はタクティックで、最初に\ ``T``\ を行ない、\ ``T``\ が生成したそれぞれのサブゴールに\ ``T'``\ を行ないます。これが\ ``;``\ の実際に一番よく使われる形です。

例えば、次の簡単な補題を考えます:

::

    Lemma foo : forall n, ble_nat 0 n = true.
    Proof.
      intros.
      destruct n.

上の証明を\ ``;``\ タクティカルを使って簡単化できます。

::

    Lemma foo' : forall n, ble_nat 0 n = true.
    Proof.
      intros.

``try``\ と\ ``;``\ の両方を使うと、ちょっと前に悩まされた証明の繰り返しを取り除くことができます。

::

    Theorem optimize_0plus_sound': forall e,
      aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e.
      induction e;

実際的にはCoqの専門家は、\ ``try``\ を\ ``induction``\ のようなタクティックと一緒に使うことで、多くの似たような「簡単な」場合を一度に処理します。これは自然に非形式的な証明に対応します。

この定理の形式的な証明の構造にマッチする非形式的な証明は次の通りです:

「定理」: すべての算術式\ ``e``\ について

::

           aeval (optimize_0plus e) = aeval e.

「証明」:``e``\ についての帰納法を使う。\ ``AMinus``\ と\ ``AMult``\ の場合は帰納仮定から直接得られる。残るのは以下の場合である:

-  ある\ ``n``\ について\ ``e = ANum n``\ とする。示すべきことは次の通りである:

   ::

             aeval (optimize_0plus (ANum n)) = aeval (ANum n).

これは\ ``optimize_0plus``\ の定義からすぐに得られる。

-  ある\ ``e1``\ と\ ``e2``\ について\ ``e = APlus e1 e2``\ とする。
   示すべきことは次の通りである:

   ::

             aeval (optimize_0plus (APlus e1 e2))
           = aeval (APlus e1 e2).

``e1``\ のとり得る形を考える。そのほとんどの場合、\ ``optimize_0plus``\ は部分式について単に自分自身を再帰的に呼び出し、\ ``e1``\ と同じ形の新しい式を再構成する。これらの場合、結果は帰納仮定からすぐに得られる。

興味深い場合は、ある\ ``n``\ について\ ``e1 = ANum n``\ であるときである。このとき\ ``n = ANum 0``\ ならば次が成立する:

::

              optimize_0plus (APlus e1 e2) = optimize_0plus e2

そして\ ``e2``\ についての帰納仮定がまさに求めるものである。一方、ある\ ``n'``\ について\ ``n = S n'``\ ならば、\ ``optimize_0plus``\ はやはり自分自身を再帰的に呼び出し、結果は帰納仮定から得られる。☐

この証明はさらに改良できます。最初の場合(``e = ANum n``\ のとき)はかなり自明です。帰納仮定からすぐに得られると言ったものより自明でしょう。それなのに完全に記述しています。これを消して、単に最初に「ほとんどの場合、すぐに、あるいは帰納仮定から直接得られる。興味深いのは\ ``APlus``\ の場合だけである...」と言った方がより良く、より明快でしょう。同じ改良を形式的な証明にも行うことができます。以下のようになります:

::

    Theorem optimize_0plus_sound'': forall e,
      aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e.
      induction e;

新しいタクティック記法を定義する
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Coqはまた、タクティックスクリプトを「プログラミングする」いろいろな方法も提供します。

-  ``Tactic Notation``\ コマンドは、「略記法タクティック」("shorthand
   tactics")
   を定義する簡単な方法を提供します。「略記法タクティック」は、呼ばれると、いろいろなタクティックを一度に適用します。
-  より洗練されたプログラミングのために、
   Coqは\ ``Ltac``\ と呼ばれる小さなビルトインのプログラミング言語と、証明の状態を調べたり変更したりするための\ ``Ltac``\ のプリミティブを提供します。その詳細はここで説明するにはちょっと複雑過ぎます(しかも、\ ``Ltac``\ がCoqの設計の一番美しくない部分だというのは共通見解です!)。しかし、詳細はリファレンスマニュアルにありますし、Coqの標準ライブラリには、読者が参考にできる\ ``Ltac``\ の定義のたくさんの例があります。
-  Coqの内部構造のより深いレベルにアクセスする新しいタクティックを作ることができる
   OCaml API
   も存在します。しかしこれは、普通のCoqユーザにとっては、苦労が報われることはほとんどありません。

``Tactic Notation``\ 機構は取り組むのに一番簡単で、多くの目的に十分なパワーを発揮します。例を挙げます。

::

    Tactic Notation "simpl_and_try" tactic(c) :=
      simpl;
      try c.

これは1つのタクティック\ ``c``\ を引数としてとる\ ``simpl_and_try``\ という新しいタクティカルを定義しています。そして、タクティック\ ``simpl; try c``\ と同値なものとして定義されます。例えば、証明内で"``simpl_and_try reflexivity.``\ "と書くことは"``simpl; try reflexivity.``\ "と書くことと同じでしょう。

次のサブセクションでは、この機構のより洗練された使い方を見ます...

場合分けを万全にする
^^^^^^^^^^^^^^^^^^^^

``induction``\ や\ ``destruct``\ で、ほとんどの場合を一度に扱えるのはとても便利ですが、またちょっと混乱もします。よく起こる問題は、このスタイルで記述された証明をメンテナンスすることが難しいということです。例えば、後で、\ ``aexp``\ の定義を拡張して、やはり特別な引数をとるコンストラクタを追加したとします。このとき上述の証明は成立しなくなっているでしょう。なぜなら、Coqは\ ``APlus``\ についてのサブゴールの前にこのコンストラクタに対応するサブゴールを生成し、その結果、\ ``APlus``\ の場合に取りかかる時には、Coqは実際にはまったく別のコンストラクタを待っていることになるからです。ここで欲しいのは、「この場所で\ ``AFoo``\ の場合を期待していましたが、証明スクリプトは\ ``APlus``\ について話しています。」という賢いエラーメッセージです。以下は、これを難なく可能にするちょっとしたトリックです。

::

    Tactic Notation "aexp_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ANum" | Case_aux c "APlus"
      | Case_aux c "AMinus" | Case_aux c "AMult" ].

(``Case_aux``\ は\ ``Case``\ 、\ ``SCase``\ 、\ ``SSCase``\ 等の共通機能を実装します。例えば、\ ``Case "foo"``\ は\ ``Case_aux Case "foo"``\ と定義されます。)

例えば、\ ``e``\ が型\ ``aexp``\ の変数のとき、

::

          aexp_cases (induction e) Case

と書くと\ ``e``\ についての帰納法を実行し(単に\ ``induction e``\ と書いたのと同じです)、そして、「その上に」、\ ``induction``\ によって生成されたそれぞれのサブゴールに\ ``Case``\ タグを付加します。このタグは、そのサブゴールがどのコンストラクタから来たかのラベルです。例えば、\ ``aexp_cases``\ を使った、\ ``optimize_0plus_sound``\ のさらに別証です:

::

    Theorem optimize_0plus_sound''': forall e,
      aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e.
      aexp_cases (induction e) Case;
        try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
        try reflexivity.

練習問題: ★★★ (optimize\_0plus\_b)
''''''''''''''''''''''''''''''''''

``optimize_0plus``\ の変換が\ ``aexp``\ の値を変えないことから、\ ``bexp``\ の値を変えずに、\ ``bexp``\ に現れる\ ``aexp``\ をすべて変換するために\ ``optimize_0plus``\ が適用できるべきでしょう。\ ``bexp``\ についてこの変換をする関数を記述しなさい。そして、それが健全であることを証明しなさい。ここまで見てきたタクティカルを使って証明を可能な限りエレガントにしなさい。

☐

練習問題: ★★★★, optional (optimizer)
''''''''''''''''''''''''''''''''''''

設計練習:
定義した\ ``optimize_0plus``\ 関数で実装された最適化は、算術式やブール式に対して考えられるいろいろな最適化の単なる1つに過ぎません。より洗練された最適化関数を記述し、その正しさを証明しなさい。

(\* FILL IN HERE \*)

☐

``omega``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~

``omega``\ タクティックは「プレスバーガー算術」(*Presburger
arithmetic*\ 、「プレスブルガー算術」とも)と呼ばれる一階述語論理のサブセットの決定手続き(decision
procedure)を実装します。William Pugh
が1992年に発明したOmegaアルゴリズムに基いています。

ゴールが以下の要素から構成された全称限量された論理式とします。以下の要素とは:

-  数値定数、加算(``+``\ と\ ``S``)、減算(``-``\ と\ ``pred``)、
   定数の積算(これがプレスバーガー算術である条件です)、
-  等式(``=``\ と\ ``<>``)および不等式(``<=``)、
-  論理演算子\ ``/\``,\ ``\/``,\ ``~``,\ ``->``

です。このとき、\ ``omega``\ を呼ぶと、ゴールを解くか、そのゴールが偽であると告げるか、いずれかになります。

::

    Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
    Proof.
      intros. omega.
    Qed.

Andrew Appel
は\ ``omega``\ を「サンタクロース・タクティック」と呼んでいます。

便利なタクティックをさらにいくつか
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

最後に、役に立ちそうないろいろなタクティックをいくつか紹介します。

-  ``clear H``: 仮定\ ``H``\ をコンテキストから消去します。
-  ``subst x``:
   コンテキストから仮定\ ``x = e``\ または\ ``e = x``\ を発見し、\ ``x``\ をコンテキストおよび現在のゴールのすべての場所で\ ``e``\ に置き換え、この仮定を消去します。
-  ``subst``:``x = e``\ および\ ``e = x``\ の形のすべての仮定を置換します。
-  ``rename... into...``: 証明コンテキストの仮定の名前を変更します。
   例えば、コンテキストが\ ``x``\ という名前の変数を含んでいるとき、\ ``rename x into y``\ は、すべての\ ``x``\ の出現を\ ``y``\ に変えます。
-  ``assumption``:
   ゴールにちょうどマッチする仮定\ ``H``\ をコンテキストから探そうとします。
   発見されたときは\ ``apply H``\ と同様に振る舞います。
-  ``contradiction``:``False``\ と同値の仮定\ ``H``\ をコンテキストから探そうとします。
   発見されたときはゴールを解きます。
-  ``constructor``:
   現在のゴールを解くのに使えるコンストラクタ\ ``c``\ を
   (現在の環境の\ ``Inductive``\ による定義から)探そうとします。発見されたときは\ ``apply c``\ と同様に振る舞います。

以降の証明でこれらのたくさんの例を見るでしょう。

関係としての評価
----------------

``aeval``\ と\ ``beval``\ を\ ``Fixpoints``\ によって定義された関数として示しました。評価について考える別の方法は、それを式と値との間の関係(*relation*)と見ることです。

この考えに立つと、算術式についてCoqの\ ``Inductive``\ による以下の定義が自然に出てきます...

::

    Module aevalR_first_try.

    Inductive aevalR : aexp -> nat -> Prop :=
      | E_ANum  : forall (n: nat),
          aevalR (ANum n) n
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
      | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (AMinus e1 e2) (n1 - n2)
      | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (AMult e1 e2) (n1 * n2).

関係についてよく行うように、\ ``aevalR``\ の中置記法を定義するのが便利です。算術式\ ``e``\ が値\ ``n``\ に評価されることを\ ``e || n``\ と書きます。(この記法は煩わしいascii記号の限界の1つです。評価関係の標準記法は二重の下向き矢印です。HTML版ではそのようにタイプセットしますが、ascii
の.v ファイルでは可能な近似として縦棒二本を使います。)

::

    Notation "e '||' n" := (aevalR e n) : type_scope.

    End aevalR_first_try.

実際は、Coqでは\ ``aevalR``\ 自身の定義中でこの記法を使うことができます。これにより、\ ``e || n``\ の形の主張を含む証明で、\ ``aevalR e n``\ という形の定義に戻らなければならない状況にならずに済みます。

このためには、最初に記法を「予約」し、それから定義と、記法が何を意味するかの宣言とを一緒に行います。

::

    Reserved Notation "e '||' n" (at level 50, left associativity).

    Inductive aevalR : aexp -> nat -> Prop :=
      | E_ANum : forall (n:nat),
          (ANum n) || n
      | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
          (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
      | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
          (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
      | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
          (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

      where "e '||' n" := (aevalR e n) : type_scope.

    Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
      | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

評価の、関係による定義と関数による定義が、すべての算術式について一致することを証明するのは簡単です...

::

    Theorem aeval_iff_aevalR : forall a n,
      (a || n) <-> aeval a = n.
    Proof.
     split.
     Case "->".
       intros H.
       aevalR_cases (induction H) SCase; simpl.
       SCase "E_ANum".
         reflexivity.
       SCase "E_APlus".
         rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
       SCase "E_AMinus".
         rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
       SCase "E_AMult".
         rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
     Case "<-".
       generalize dependent n.
       aexp_cases (induction a) SCase;
          simpl; intros; subst.
       SCase "ANum".
         apply E_ANum.
       SCase "APlus".
         apply E_APlus.
          apply IHa1. reflexivity.
          apply IHa2. reflexivity.
       SCase "AMinus".
         apply E_AMinus.
          apply IHa1. reflexivity.
          apply IHa2. reflexivity.
       SCase "AMult".
         apply E_AMult.
          apply IHa1. reflexivity.
          apply IHa2. reflexivity.
    Qed.

タクティカルをより積極的に使ったより短い証明です:

::

    Theorem aeval_iff_aevalR' : forall a n,
      (a || n) <-> aeval a = n.
    Proof.

練習問題: ★★, optional (bevalR)
'''''''''''''''''''''''''''''''

関係\ ``bevalR``\ を\ ``aevalR``\ と同じスタイルで記述し、それが\ ``beval``\ と同値であることを証明しなさい。

☐

::

    *)

算術式とブール式の評価の定義について、関数を使うか関係を使うかはほとんど趣味の問題です。一般に、Coqは関係を扱う方がいくらかサポートが厚いです。特に帰納法についてはそうです。一方、ある意味で関数による定義の方がより多くの情報を持っています。なぜなら、関数は決定的でなければならず、またすべての引数について定義されていなければなりません。関数については、必要ならばこれらの性質を明示的に示さなければなりません。

しかしながら、評価の定義として、関係による定義が関数による定義よりはるかに望ましい状況があります。以下で簡単に見ます。

推論規則記法
~~~~~~~~~~~~

非形式的な議論には、\ ``aevalR``\ や似たような関係についての規則を、推論規則(*inference
rules*)と呼ばれる、より読みやすいグラフィカルな形で書くのが便利です。推論規則は、横線の上の前提から、横線の下の結論を導出できることを述べます。例えば、コンストラクタ\ ``E_APlus``...

::

          | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
              aevalR e1 n1 ->
              aevalR e2 n2 ->
              aevalR (APlus e1 e2) (n1 + n2)

...は推論規則として次のように書けるでしょう:

::

                                   e1 || n1
                                   e2 || n2
                             --------------------                         (E_APlus)
                             APlus e1 e2 || n1+n2

形式的には、推論規則について何も深いものはありません。単なる含意です。右に書かれた規則名はコンストラクタで、横線より上の前提の間の各改行と横線自体は\ ``->``\ と読むことができます。規則で言及されるすべての変数(``e1``\ 、\ ``n1``\ 等)は暗黙のうちに冒頭で全称限量子に束縛されています。規則の集合全体は\ ``Inductive``\ 宣言で囲われていると理解されます(これは完全に暗黙のまま置かれるか、非形式的に「\ ``aevalR``\ は以下の規則について閉じた最小の関係とします...」などと述べられるかします)。

例えば、\ ``||``\ は以下の規則について閉じた最小の関係です:

::

                                 -----------                               (E_ANum)
                                 ANum n || n

                                   e1 || n1
                                   e2 || n2
                             --------------------                         (E_APlus)
                             APlus e1 e2 || n1+n2

                                   e1 || n1
                                   e2 || n2
                            ---------------------                        (E_AMinus)
                            AMinus e1 e2 || n1-n2

                                   e1 || n1
                                   e2 || n2
                             --------------------                         (E_AMult)
                             AMult e1 e2 || n1*n2

    End AExp.

変数を持つ式
------------

さて、Impの定義に戻りましょう。次にしなければならないことは、算術式とブール式に変数を拡張することです。話を単純にするため、すべての変数はグローバルで、数値だけを持つとしましょう。

識別子
~~~~~~

始めに、プログラム変数などの識別子(*identifiers*)を形式化しなければなりません。このために文字列を使うこともできるでしょうし、(実際のコンパイラでは)シンボルテーブルへのポインタのようなある種の特別な構造を使うこともできるでしょう。しかし、簡単にするため、識別子に単に自然数を使います。

(このセクションをモジュールに隠します。それは、これらの定義が実際には\ ``SfLib_J.v``\ にあるからです。しかし説明のためにここで繰り返します。)

::

    Module Id.

新しいデータタイプ\ ``Id``\ を定義して、識別子と数値を混乱しないようにします。

::

    Inductive id : Type :=
      Id : nat -> id.

    Definition beq_id X1 X2 :=
      match (X1, X2) with
        (Id n1, Id n2) => beq_nat n1 n2
      end.

さて、この方法で「覆った」数値を識別子としたので、数値のいくつかの性質を、対応する識別子の性質として繰り返しておくのが便利です。そうすると、定義や証明の中の識別子を、覆いを開いて中の数値を晒すことなく抽象的に扱うことができます。識別子について知らなければならないことは、識別子同士が同じか違うかだけなので、本当に2、3のことだけが必要です。

::

    Theorem beq_id_refl : forall X,
      true = beq_id X X.
    Proof.
      intros. destruct X.
      apply beq_nat_refl.  Qed.

練習問題: ★, optional (beq\_id\_eq)
'''''''''''''''''''''''''''''''''''

この問題とそれに続く練習問題では、帰納法を使わずに、既に証明した自然数の同様の結果を適用しなさい。上述したいくつかのタクティックが使えるかもしれません。

::

    Theorem beq_id_eq : forall i1 i2,
      true = beq_id i1 i2 -> i1 = i2.
    Proof.
       Admitted.

☐

練習問題: ★, optional (beq\_id\_false\_not\_eq)
'''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem beq_id_false_not_eq : forall i1 i2,
      beq_id i1 i2 = false -> i1 <> i2.
    Proof.
       Admitted.

☐

練習問題: ★, optional (not\_eq\_beq\_id\_false)
'''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem not_eq_beq_id_false : forall i1 i2,
      i1 <> i2 -> beq_id i1 i2 = false.
    Proof.
       Admitted.

☐

練習問題: ★, optional (beq\_id\_sym)
''''''''''''''''''''''''''''''''''''

::

    Theorem beq_id_sym: forall i1 i2,
      beq_id i1 i2 = beq_id i2 i1.
    Proof.
       Admitted.

☐

::

    End Id.

状態
~~~~

状態(*state*)はプログラムの実行のある時点のすべての変数の現在値を表します。

簡単にするため(部分関数を扱うのを避けるため)、どのようなプログラムも有限個の変数しか使わないにもかかわらず、状態はすべての変数について値を定義しているものとします。

::

    Definition state := id -> nat.

    Definition empty_state : state :=
      fun _ => 0.

    Definition update (st : state) (X:id) (n : nat) : state :=
      fun X' => if beq_id X X' then n else st X'.

``update``\ についての単純な性質が必要です。

練習問題: ★★, optional (update\_eq)
'''''''''''''''''''''''''''''''''''

::

    Theorem update_eq : forall n X st,
      (update st X n) X = n.
    Proof.
       Admitted.

☐

練習問題: ★★, optional (update\_neq)
''''''''''''''''''''''''''''''''''''

::

    Theorem update_neq : forall V2 V1 n st,
      beq_id V2 V1 = false ->
      (update st V2 n) V1 = (st V1).
    Proof.
       Admitted.

☐

練習問題: ★★, optional (update\_example)
''''''''''''''''''''''''''''''''''''''''

タクティックを使って遊び始める前に、定理が言っていることを正確に理解していることを確認しなさい!

::

    Theorem update_example : forall (n:nat),
      (update empty_state (Id 2) n) (Id 3) = 0.
    Proof.
       Admitted.

☐

練習問題: ★★ (update\_shadow)
'''''''''''''''''''''''''''''

::

    Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
       (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
    Proof.
       Admitted.

☐

練習問題: ★★, optional (update\_same)
'''''''''''''''''''''''''''''''''''''

::

    Theorem update_same : forall x1 k1 k2 (f : state),
      f k1 = x1 ->
      (update f k1 x1) k2 = f k2.
    Proof.
       Admitted.

☐

練習問題: ★★, optional (update\_permute)
''''''''''''''''''''''''''''''''''''''''

::

    Theorem update_permute : forall x1 x2 k1 k2 k3 f,
      beq_id k2 k1 = false ->
      (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
    Proof.
       Admitted.

☐

構文
~~~~

前に定義した算術式に、単にもう1つコンストラクタを追加することで変数を追加できます:

::

    Inductive aexp : Type :=
      | ANum : nat -> aexp
      | AId : id -> aexp

変数の略記法:

::

    Definition X : id := Id 0.
    Definition Y : id := Id 1.
    Definition Z : id := Id 2.

(プログラム変数のこの慣習(``X``,\ ``Y``,\ ``Z``)は、型に大文字の記号を使うという以前の使用法と衝突します。コースのこの部分では多相性を多用はしないので、このことが混乱を招くことはないはずです。)

``bexp``\ の定義は前と同じです(ただし新しい\ ``aexp``\ を使います):

::

    Inductive bexp : Type :=
      | BTrue : bexp
      | BFalse : bexp
      | BEq : aexp -> aexp -> bexp
      | BLe : aexp -> aexp -> bexp
      | BNot : bexp -> bexp
      | BAnd : bexp -> bexp -> bexp.

    Tactic Notation "bexp_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
      | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

評価
~~~~

算術とブールの評価器は、自明な方法で変数を扱うように拡張されます:

::

    Fixpoint aeval (st : state) (e : aexp) : nat :=
      match e with
      | ANum n => n
      | AId X => st X

コマンド
--------

さて、Imp コマンド (または主張) の構文と挙動を定義する準備が出来ました

構文
~~~~

非形式的には、コマンドは以下の BNF で表現されます。構文:

::

         com ::= 'SKIP'
               | X '::=' aexp
               | com ';' com
               | 'WHILE' bexp 'DO' com 'END'
               | 'IFB' bexp 'THEN' com 'ELSE' com 'FI'

例えば、Imp における階乗関数は以下のようになります。

::

         Z ::= X;
         Y ::= 1;
         WHILE not (Z = 0) DO
           Y ::= Y * Z;
           Z ::= Z - 1
         END

このコマンドが終わったとき、変数\ ``Y``\ は変数\ ``X``\ の階乗の値を持つでしょう。

以下に、コマンドの構文の形式的な定義を示します。

::

    Inductive com : Type :=
      | CSkip : com
      | CAss : id -> aexp -> com
      | CSeq : com -> com -> com
      | CIf : bexp -> com -> com -> com
      | CWhile : bexp -> com -> com.

    Tactic Notation "com_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
      | Case_aux c "IFB" | Case_aux c "WHILE" ].

いつものとおり、より読みやすいよう、いくつかの\ ``Notation``\ 宣言が使えます。しかし、Coq
の組み込みの表記と衝突しないよう、少し気をつける必要があります(手軽さを維持しつつ！)。特に、\ ``aexp``\ と\ ``bexp``\ については、すでに定義した数値演算子やブール演算子との混同を避けるために、新しい表記は導入しません。(同様の理由により、条件文に対しては通常使われる\ ``IF``\ の代わりに\ ``IFB``\ というキーワードを使います。)

::

    Notation "'SKIP'" :=
      CSkip.
    Notation "X '::=' a" :=
      (CAss X a) (at level 60).
    Notation "c1 ; c2" :=
      (CSeq c1 c2) (at level 80, right associativity).
    Notation "'WHILE' b 'DO' c 'END'" :=
      (CWhile b c) (at level 80, right associativity).
    Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
      (CIf e1 e2 e3) (at level 80, right associativity).

例えば先の階乗関数を Coq
での形式的な定義として記述し直すと、以下のようになります。

::

    Definition fact_in_coq : com :=
      Z ::= AId X;
      Y ::= ANum 1;
      WHILE BNot (BEq (AId Z) (ANum 0)) DO
        Y ::= AMult (AId Y) (AId Z);
        Z ::= AMinus (AId Z) (ANum 1)
      END.

例
~~

以下に、さらなる例を挙げます。

割り当て:

::

    Definition plus2 : com :=
      X ::= (APlus (AId X) (ANum 2)).

    Definition XtimesYinZ : com :=
      Z ::= (AMult (AId X) (AId Y)).

    Definition subtract_slowly_body : com :=
      Z ::= AMinus (AId Z) (ANum 1) ;
      X ::= AMinus (AId X) (ANum 1).

ループ:

::

    Definition subtract_slowly : com :=
      WHILE BNot (BEq (AId X) (ANum 0)) DO
        subtract_slowly_body
      END.

    Definition subtract_3_from_5_slowly : com :=
      X ::= ANum 3 ;
      Z ::= ANum 5 ;
      subtract_slowly.

無限ループ:

::

    Definition loop : com :=
      WHILE BTrue DO
        SKIP
      END.

階乗関数再び
(あとで戻って証明するとき便利なように、細かい部品に分割してあります)。

::

    Definition fact_body : com :=
      Y ::= AMult (AId Y) (AId Z) ;
      Z ::= AMinus (AId Z) (ANum 1).

    Definition fact_loop : com :=
      WHILE BNot (BEq (AId Z) (ANum 0)) DO
        fact_body
      END.

    Definition fact_com : com :=
      Z ::= AId X ;
      Y ::= ANum 1 ;
      fact_loop.

評価
----

次に、Imp
のコマンドの実行が何を意味するかを定義する必要があります。\ ``WHILE``\ ループは、これを少々扱いにくいものにしています
...

評価関数
~~~~~~~~

以下は\ ``WHILE``\ 以外のコマンドの評価関数を得ようとした、最初の試みです。

::

    Fixpoint ceval_step1 (st : state) (c : com) : state :=
      match c with
        | SKIP =>
            st
        | l ::= a1 =>
            update st l (aeval st a1)
        | c1 ; c2 =>
            let st' := ceval_step1 st c1 in
            ceval_step1 st' c2
        | IFB b THEN c1 ELSE c2 FI =>
            if (beval st b)
              then ceval_step1 st c1
              else ceval_step1 st c2
        | WHILE b1 DO c1 END =>
            st

次の試みでは、評価が常に停止することを保証するため、数の引数を追加して「ステップ指数」として用いています。

::

    Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
      match i with
      | O => empty_state
      | S i' =>
        match c with
          | SKIP =>
              st
          | l ::= a1 =>
              update st l (aeval st a1)
          | c1 ; c2 =>
              let st' := ceval_step2 st c1 i' in
              ceval_step2 st' c2 i'
          | IFB b THEN c1 ELSE c2 FI =>
              if (beval st b)
                then ceval_step2 st c1 i'
                else ceval_step2 st c2 i'
          | WHILE b1 DO c1 END =>
              if (beval st b1)
              then let st' := ceval_step2 st c1 i' in
                   ceval_step2 st' c i'
              else st
        end
      end.

注:
ここでの指数\ ``i``\ は「評価のステップ数」を数えるものだろうか？という点が気になります。しかしよく見ると、そうではないと分かります。例えば、直列実行に対する規則では、2
つの再帰呼び出しに同じ\ ``i``\ が渡されています。\ ``i``\ がどのように扱われているのかを正確に理解することは、以下で演習問題として与えられている\ ``ceval__ceval_step``\ の証明で重要となるでしょう。

3
つ目の試みでは、単なる\ ``state``\ の代わりに\ ``option state``\ を返すようにしています。こうすると、通常終了と異常終了を区別出来ます。

::

    Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                        : option state :=
      match i with
      | O => None
      | S i' =>
        match c with
          | SKIP =>
              Some st
          | l ::= a1 =>
              Some (update st l (aeval st a1))
          | c1 ; c2 =>
              match (ceval_step3 st c1 i') with
              | Some st' => ceval_step3 st' c2 i'
              | None => None
              end
          | IFB b THEN c1 ELSE c2 FI =>
              if (beval st b)
                then ceval_step3 st c1 i'
                else ceval_step3 st c2 i'
          | WHILE b1 DO c1 END =>
              if (beval st b1)
              then match (ceval_step3 st c1 i') with
                   | Some st' => ceval_step3 st' c i'
                   | None => None
                   end
              else Some st
        end
      end.

オプション状態に対する場合分けに繰り返し含まれている「配管」を隠すための、補助的なちょっとした記法を導入すると、この定義の読みやすさは改善出来ます。

::

    Notation "'LETOPT' x <== e1 'IN' e2"
       := (match e1 with
             | Some x => e2
             | None => None
           end)
       (right associativity, at level 60).

    Fixpoint ceval_step (st : state) (c : com) (i : nat)
                        : option state :=
      match i with
      | O => None
      | S i' =>
        match c with
          | SKIP =>
              Some st
          | l ::= a1 =>
              Some (update st l (aeval st a1))
          | c1 ; c2 =>
              LETOPT st' <== ceval_step st c1 i' IN
              ceval_step st' c2 i'
          | IFB b THEN c1 ELSE c2 FI =>
              if (beval st b)
                then ceval_step st c1 i'
                else ceval_step st c2 i'
          | WHILE b1 DO c1 END =>
              if (beval st b1)
              then LETOPT st' <== ceval_step st c1 i' IN
                   ceval_step st' c i'
              else Some st
        end
      end.

    Definition test_ceval (st:state) (c:com) :=
      match ceval_step st c 500 with
      | None    => None
      | Some st => Some (st X, st Y, st Z)
      end.

練習問題: ★★, recommended (pup\_to\_n)
''''''''''''''''''''''''''''''''''''''

``1``\ から\ ``X``\ までの整数を変数\ ``Y``\ に足す
(つまり\ ``1 + 2 + ... + X``)Imp
プログラムを書きなさい。下に示したテストを満たすことを確認しなさい。

::

    Definition pup_to_n : com :=

☐

練習問題: ★★, optional (peven)
''''''''''''''''''''''''''''''

``X``\ が偶数だったら\ ``Z``\ に\ ``0``\ を、そうでなければ\ ``Z``\ に\ ``1``\ をセットする\ ``While``\ プログラムを書きなさい。テストには\ ``ceval_test``\ を使いなさい。

☐

関係としての評価
~~~~~~~~~~~~~~~~

ここに改善策があります:``ceval``\ を関数ではなく関係 (*relation*)
として定義しましょう。つまり、上の\ ``aevalR``\ と\ ``bevalR``\ と同様に\ ``Type``\ ではなく\ ``Prop``\ で定義しましょう。

これは重要な変更です。ステップ指数をすべての場所で引き回す馬鹿馬鹿しさから解放してくれるのに加え、定義での柔軟性を与えてくれます。例えば、もし言語に並行性の要素を導入したら、評価の定義を非決定的に書きたくなるでしょう。つまり、その関数は全関数でないだけでなく、部分関数ですらないかも知れません！

``ceavl``\ 関係に対する表記として\ ``c / st || st'``\ を使います。正確に言うと、\ ``c / st || st'``\ と書いたらプログラム\ ``c``\ を初期状態\ ``st``\ で評価すると、その結果は最終状態\ ``st'``\ になる、ということを意味します。これは「\ ``c``\ は状態\ ``st``\ を\ ``st'``\ に持っていく」とも言えます。

::

                               ----------------                            (E_Skip)
                               SKIP / st || st

                               aeval st a1 = n
                       --------------------------------                     (E_Ass)
                       l := a1 / st || (update st l n)

                               c1 / st || st'
                              c2 / st' || st''
                             -------------------                            (E_Seq)
                             c1;c2 / st || st''

                              beval st b1 = true
                               c1 / st || st'
                    -------------------------------------                (E_IfTrue)
                    IF b1 THEN c1 ELSE c2 FI / st || st'

                             beval st b1 = false
                               c2 / st || st'
                    -------------------------------------               (E_IfFalse)
                    IF b1 THEN c1 ELSE c2 FI / st || st'

                             beval st b1 = false
                        ------------------------------                 (E_WhileEnd)
                        WHILE b1 DO c1 END / st || st

                              beval st b1 = true
                               c1 / st || st'
                      WHILE b1 DO c1 END / st' || st''
                      ---------------------------------               (E_WhileLoop)
                        WHILE b1 DO c1 END / st || st''

以下に形式的な定義を挙げます。(上の推論規則とどのように対応するか、確認しておきましょう。)

::

    Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

    Inductive ceval : com -> state -> state -> Prop :=
      | E_Skip : forall st,
          SKIP / st || st
      | E_Ass  : forall st a1 n l,
          aeval st a1 = n ->
          (l ::= a1) / st || (update st l n)
      | E_Seq : forall c1 c2 st st' st'',
          c1 / st  || st' ->
          c2 / st' || st'' ->
          (c1 ; c2) / st || st''
      | E_IfTrue : forall st st' b1 c1 c2,
          beval st b1 = true ->
          c1 / st || st' ->
          (IFB b1 THEN c1 ELSE c2 FI) / st || st'
      | E_IfFalse : forall st st' b1 c1 c2,
          beval st b1 = false ->
          c2 / st || st' ->
          (IFB b1 THEN c1 ELSE c2 FI) / st || st'
      | E_WhileEnd : forall b1 st c1,
          beval st b1 = false ->
          (WHILE b1 DO c1 END) / st || st
      | E_WhileLoop : forall st st' st'' b1 c1,
          beval st b1 = true ->
          c1 / st || st' ->
          (WHILE b1 DO c1 END) / st' || st'' ->
          (WHILE b1 DO c1 END) / st || st''

      where "c1 '/' st '||' st'" := (ceval c1 st st').

    Tactic Notation "ceval_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
      | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
      | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

評価を関数ではなく関係として定義することのコストは、あるプログラムを実行した結果がとある状態になる、というのを
Coq
の計算機構にやってもらうだけではなく、その「証明」を構築する必要がある、ということです。

::

    Example ceval_example1:
        (X ::= ANum 2;
         IFB BLe (AId X) (ANum 1)
           THEN Y ::= ANum 3
           ELSE Z ::= ANum 4
         FI)
       / empty_state
       || (update (update empty_state X 2) Z 4).
    Proof.

練習問題: ★★ (ceval\_example2)
''''''''''''''''''''''''''''''

::

    Example ceval_example2:
        (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
        (update (update (update empty_state X 0) Y 1) Z 2).
    Proof.
       Admitted.

☐

関係による評価とステップ指数を利用した評価の等価性
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

算術式とブール式で行ったように、2
つの評価の定義が本当に、結局のところ同じものになるのかを確認したくなるでしょう。この章では、それを確認します。定理の主張を理解して、証明の構造を追えることを確認しておいて下さい。

::

    Theorem ceval_step__ceval: forall c st st',
          (exists i, ceval_step st c i = Some st') ->
          c / st || st'.
    Proof.
      intros c st st' H.
      inversion H as [i E].
      clear H.
      generalize dependent st'.
      generalize dependent st.
      generalize dependent c.
      induction i as [| i' ].

      Case "i = 0 -- contradictory".
        intros c st st' H. inversion H.

      Case "i = S i'".
        intros c st st' H.
        com_cases (destruct c) SCase;
               simpl in H; inversion H; subst; clear H.
          SCase "SKIP". apply E_Skip.
          SCase "::=". apply E_Ass. reflexivity.

          SCase ";".
            remember (ceval_step st c1 i') as r1. destruct r1.
            SSCase "Evaluation of r1 terminates normally".
              apply E_Seq with s.
                apply IHi'. rewrite Heqr1. reflexivity.
                apply IHi'. simpl in H1. assumption.
            SSCase "Otherwise -- contradiction".
              inversion H1.

          SCase "IFB".
            remember (beval st b) as r. destruct r.
            SSCase "r = true".
              apply E_IfTrue. rewrite Heqr. reflexivity.
              apply IHi'. assumption.
            SSCase "r = false".
              apply E_IfFalse. rewrite Heqr. reflexivity.
              apply IHi'. assumption.

          SCase "WHILE". remember (beval st b) as r. destruct r.
            SSCase "r = true".
              remember (ceval_step st c i') as r1. destruct r1.
              SSSCase "r1 = Some s".
                apply E_WhileLoop with s. rewrite Heqr. reflexivity.
                apply IHi'. rewrite Heqr1. reflexivity.
                apply IHi'. simpl in H1. assumption.
              SSSCase "r1 = None".
                inversion H1.
            SSCase "r = false".
              inversion H1.
              apply E_WhileEnd.
              rewrite Heqr. subst. reflexivity.  Qed.

練習問題: ★★★★ (ceval\_step\_\_ceval\_inf)
''''''''''''''''''''''''''''''''''''''''''

いつものテンプレートにのっとって、\ ``ceval_step__ceval``\ の形式的でない証明を書きましょう。(帰納的に定義された値の場合分けに対するテンプレートは、帰納法の仮定がないこと以外は帰納法と同じ見た目になるはずです。)単に形式的な証明のステップを書き写すだけでなく、人間の読者に主要な考えが伝わるようにしなさい。

(\* FILL IN HERE \*)☐

::

    Theorem ceval_step_more: forall i1 i2 st st' c,
      i1 <= i2 ->
      ceval_step st c i1 = Some st' ->
      ceval_step st c i2 = Some st'.
    Proof.
    induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
      Case "i1 = 0".
        inversion Hceval.
      Case "i1 = S i1'".
        destruct i2 as [|i2']. inversion Hle.
        assert (Hle': i1' <= i2') by omega.
        com_cases (destruct c) SCase.
        SCase "SKIP".
          simpl in Hceval. inversion Hceval.
          reflexivity.
        SCase "::=".
          simpl in Hceval. inversion Hceval.
          reflexivity.
        SCase ";".
          simpl in Hceval. simpl.
          remember (ceval_step st c1 i1') as st1'o.
          destruct st1'o.
          SSCase "st1'o = Some".
            symmetry in Heqst1'o.
            apply (IHi1' i2') in Heqst1'o; try assumption.
            rewrite Heqst1'o. simpl. simpl in Hceval.
            apply (IHi1' i2') in Hceval; try assumption.
          SSCase "st1'o = None".
            inversion Hceval.

        SCase "IFB".
          simpl in Hceval. simpl.
          remember (beval st b) as bval.
          destruct bval; apply (IHi1' i2') in Hceval; assumption.

        SCase "WHILE".
          simpl in Hceval. simpl.
          destruct (beval st b); try assumption.
          remember (ceval_step st c i1') as st1'o.
          destruct st1'o.
          SSCase "st1'o = Some".
            symmetry in Heqst1'o.
            apply (IHi1' i2') in Heqst1'o; try assumption.
            rewrite -> Heqst1'o. simpl. simpl in Hceval.
            apply (IHi1' i2') in Hceval; try assumption.
          SSCase "i1'o = None".
            simpl in Hceval. inversion Hceval.  Qed.

練習問題: ★★★, recommended (ceval\_\_ceval\_step)
'''''''''''''''''''''''''''''''''''''''''''''''''

以下の証明を完成させなさい。何度か\ ``ceval_step_more``\ が必要となり、さらに\ ``<=``\ と\ ``plus``\ に関するいくつかの基本的な事実が必要となるでしょう。

::

    Theorem ceval__ceval_step: forall c st st',
          c / st || st' ->
          exists i, ceval_step st c i = Some st'.
    Proof.
      intros c st st' Hce.
      ceval_cases (induction Hce) Case.
       Admitted.

☐

::

    Theorem ceval_and_ceval_step_coincide: forall c st st',
          c / st || st'
      <-> exists i, ceval_step st c i = Some st'.
    Proof.
      intros c st st'.
      split. apply ceval__ceval_step. apply ceval_step__ceval.
    Qed.

実行の決定性
~~~~~~~~~~~~

評価の定義を計算的なものから関係的なものに変更するのは、評価は全関数であるべきという
(Fixpoint の定義におけるCoq の制限によって課せられる)
不自然な要求から逃れさせてくれる良い変更です。しかしこれは、2
つ目の評価の定義は本当に部分関数なのか？という疑問ももたらします。つまり、同じ状態\ ``st``\ から始めて、あるコマンド\ ``c``\ を違った方法で評価し、2
つの異なる出力状態\ ``st'``\ と\ ``st''``\ に至るのは可能か？ということです。

実際には、こうなることはありません。評価関係\ ``ceval``\ は部分関数です。以下に証明を挙げます:

::

    Theorem ceval_deterministic: forall c st st1 st2,
         c / st || st1  ->
         c / st || st2 ->
         st1 = st2.
    Proof.
      intros c st st1 st2 E1 E2.
      generalize dependent st2.
      ceval_cases (induction E1) Case;
               intros st2 E2; inversion E2; subst.
      Case "E_Skip". reflexivity.
      Case "E_Ass". reflexivity.
      Case "E_Seq".
        assert (st' = st'0) as EQ1.
          SCase "Proof of assertion". apply IHE1_1; assumption.
        subst st'0.
        apply IHE1_2. assumption.
      Case "E_IfTrue".
        SCase "b1 evaluates to true".
          apply IHE1. assumption.
        SCase "b1 evaluates to false (contradiction)".
          rewrite H in H5. inversion H5.
      Case "E_IfFalse".
        SCase "b1 evaluates to true (contradiction)".
          rewrite H in H5. inversion H5.
        SCase "b1 evaluates to false".
          apply IHE1. assumption.
      Case "E_WhileEnd".
        SCase "b1 evaluates to true".
          reflexivity.
        SCase "b1 evaluates to false (contradiction)".
          rewrite H in H2. inversion H2.
      Case "E_WhileLoop".
        SCase "b1 evaluates to true (contradiction)".
          rewrite H in H4. inversion H4.
        SCase "b1 evaluates to false".
          assert (st' = st'0) as EQ1.
            SSCase "Proof of assertion". apply IHE1_1; assumption.
          subst st'0.
          apply IHE1_2. assumption.  Qed.

以下に、より巧みな証明を示します。これは関係による定義と指数を利用した定義の評価が同じである事実を利用しています。

::

    Theorem ceval_deterministic' : forall c st st1 st2,
         c / st || st1  ->
         c / st || st2 ->
         st1 = st2.
    Proof.
      intros c st st1 st2 He1 He2.
      apply ceval__ceval_step in He1.
      apply ceval__ceval_step in He2.
      inversion He1 as [i1 E1].
      inversion He2 as [i2 E2].
      apply ceval_step_more with (i2 := i1 + i2) in E1.
      apply ceval_step_more with (i2 := i1 + i2) in E2.
      rewrite E1 in E2. inversion E2. reflexivity.
      omega. omega.  Qed.

プログラムの検証
----------------

ここから Imp
におけるプログラムの検証に対する系統だったテクニックに深く関わっていきます。しかし、その多くはむき出しの
(もとの) 定義を扱うだけで出来ます。この章では、いくつかの例を探します。

基本的な例
~~~~~~~~~~

::

    Theorem plus2_spec : forall st n st',
      st X = n ->
      plus2 / st || st' ->
      st' X = n + 2.
    Proof.
      intros st n st' HX Heval.

練習問題: ★★★, recommended (XtimesYinZ\_spec)
'''''''''''''''''''''''''''''''''''''''''''''

XtimesYinZ の Imp プログラムの仕様を書いて証明しなさい。

☐

練習問題: ★★★, recommended (loop\_never\_stops)
'''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem loop_never_stops : forall st st',
      ~(loop / st || st').
    Proof.
      intros st st' contra. unfold loop in contra.
      remember (WHILE BTrue DO SKIP END) as loopdef.
       Admitted.

☐

::

    Fixpoint no_whiles (c : com) : bool :=
      match c with
      | SKIP       => true
      | _ ::= _    => true
      | c1 ; c2  => andb (no_whiles c1) (no_whiles c2)
      | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
      | WHILE _ DO _ END  => false
      end.

練習問題: ★★, optional (no\_whilesR)
''''''''''''''''''''''''''''''''''''

性質\ ``no_whiles``\ はプログラムが while
ループを含まない場合\ ``true``\ を返します。Inductive
を使って\ ``c``\ が while
ループのないプログラムのとき証明可能な性質\ ``no_whilesR``\ を書きなさい。さらに、それが\ ``no_whiles``\ と等価であることを示しなさい。

::

    Inductive no_whilesR: com -> Prop :=
      Admitted.

☐

練習問題: ★★★★, optional (no\_whiles\_terminating)
''''''''''''''''''''''''''''''''''''''''''''''''''

while ループを含まない Imp
プログラムは必ず停止します。これを定理として記述し、証明しなさい。

(``no_whiles``\ と\ ``no_whilesR``\ のどちらでも好きなほうを使いなさい。)

☐

プログラム正当性 (Optional)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

階乗のプログラムを思い出しましょう:

::

    Print fact_body. Print fact_loop. Print fact_com.

階乗関数の別の「数学的な」定義を以下に示します:

::

    Fixpoint real_fact (n:nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (real_fact n')
      end.

変数\ ``X``\ がある数\ ``x``\ を持つ状態で\ ``fact_com``\ を実行すると、変数\ ``Y``\ が\ ``x``\ の階乗の値を持つ状態で停止する、ということを示したくなります。これを示すため、ループ不変式
(*loop invariant*) という重要な概念を使います。

::

    Definition fact_invariant (x:nat) (st:state) :=
      (st Y) * (real_fact (st Z)) = real_fact x.

    Theorem fact_body_preserves_invariant: forall st st' x,
         fact_invariant x st ->
         st Z <> 0 ->
         fact_body / st || st' ->
         fact_invariant x st'.
    Proof.
      unfold fact_invariant, fact_body.
      intros st st' x Hm HZnz He.
      inversion He; subst; clear He.
      inversion H1; subst; clear H1.
      inversion H4; subst; clear H4.
      unfold update. simpl.

これらをすべてつなぎ合わせましょう...

::

    Theorem fact_com_correct : forall st st' x,
         st X = x ->
         fact_com / st || st' ->
         st' Y = real_fact x.
    Proof.
      intros st st' x HX Hce.
      inversion Hce; subst; clear Hce.
      inversion H1; subst; clear H1.
      inversion H4; subst; clear H4.
      inversion H1; subst; clear H1.
      rename st' into st''. simpl in H5.

この、状態をつっついて定義を展開するような全体のやり方を、何かより強力な補題や、より一貫性のある推論原理で改善できないのかと思う人もいるかもしれません。実は、それがまさに次の章(``Hoare_J.v``)の主題です!

練習問題: ★★★★, optional (subtract\_slowly\_spec)
'''''''''''''''''''''''''''''''''''''''''''''''''

上の\ ``fact_com``\ の仕様、および以下の不変式をガイドとして、subtract\_slowly
の仕様を証明しなさい。

::

    Definition ss_invariant (x:nat) (z:nat) (st:state) :=
      minus (st Z) (st X) = minus z x.

☐

追加の練習問題
--------------

練習問題: ★★★★, optional (add\_for\_loop)
'''''''''''''''''''''''''''''''''''''''''

C
風の\ ``for``\ ループをコマンドの言語に追加し、\ ``ceval``\ の定義を\ ``for``\ ループの意味も与えるよう更新して、このファイルにあるすべての証明が
Coq
に通るよう、必要なところへ\ ``for``\ ループに対する場合分けを追加しなさい。

``for``\ ループは (a) 初めに実行される主張、(b)
各繰り返しで実行される、ループを続けてよいか決定するテスト、(c)
各ループの繰り返しの最後に実行される主張、および(d)
ループの本体を構成する主張によってパラメタ化されていなければなりません。(``for``\ ループに対する具体的な表記の構成を気にする必要はありませんが、やりたければ自由にやって構いません。)

☐

練習問題: ★★★, optional (short\_circuit)
''''''''''''''''''''''''''''''''''''''''

多くのモダンなプログラミング言語はブール演算子\ ``and``\ に対し、「省略した」実行を使っています。\ ``BAnd b1 b2``\ を実行するには、まず\ ``b1``\ を評価します。それが\ ``false``\ に評価されるならば、\ ``b2``\ の評価はせず、すぐに\ ``BAnd``\ 式全体の結果を\ ``false``\ に評価します。そうでなければ、\ ``BAnd``\ 式の結果を決定するため、\ ``b2``\ が評価されます。

このように\ ``BAnd``\ を省略して評価する、別のバージョンの\ ``beval``\ を書き、それが\ ``beavl``\ と等価であることを証明しなさい。

練習問題: ★★★★, recommended (stack\_compiler)
'''''''''''''''''''''''''''''''''''''''''''''

HP の電卓、Forth や Postscript などのプログラミング言語、および Java
Virtual Machine
などの抽象機械はすべて、スタックを使って算術式を評価します。例えば、

::

       (2*3)+(3*(4-2))

という式は

::

       2 3 * 3 4 2 - * +

と入力され、以下のように実行されるでしょう:

::

      []            |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

この練習問題のタスクは、\ ``eaxp``\ をスタック機械の命令列に変換する小さなコンパイラを書き、その正当性を証明することです。

スタック言語の命令セットは、以下の命令から構成されます:

-  ``SPush n``: 数\ ``n``\ をスタックにプッシュする。
-  ``SLoad X``:
   ストアから識別子\ ``X``\ に対応する値を読み込み、スタックにプッシュする。
-  ``SPlus``: スタックの先頭の 2 つの数をポップし、それらを足して、
   結果をスタックにプッシュする。
-  ``SMinus``: 上と同様。ただし引く。
-  ``SMult``: 上と同様。ただし掛ける。

   Inductive sinstr : Type := \| SPush : nat -> sinstr \| SLoad : id ->
   sinstr \| SPlus : sinstr \| SMinus : sinstr \| SMult : sinstr.

スタック言語のプログラムを評価するための関数を書きなさい。入力として、状態、数のリストとして表現されたスタック(スタックの先頭要素はリストの先頭)、および命令のリストとして表現されたプログラムを受け取り、受け取ったプログラムの実行した後のスタックを返します。下にある例で、その関数のテストをしなさい。

上の仕様では、スタックが 2
つ未満の要素しか含まずに\ ``SPlus``\ や\ ``SMinus``\ 、\ ``SMult``\ 命令に至った場合を明示していないままなことに注意しましょう。我々のコンパイラはそのような奇形のプログラムは生成しないので、これは重要でないという意味です。しかし正当性の証明をするときは、いくつかの選択のほうが証明をより簡単にすることに気づくかもしれません。

::

    Fixpoint s_execute (st : state) (stack : list nat)
                       (prog : list sinstr)
                     : list nat :=

次に、\ ``aexp``\ をスタック機械のプログラムにコンパイルする関数を書きなさい。このプログラムを実行する影響は、もとの式の値をスタックに積むことと同じでなければなりません。

::

    Fixpoint s_compile (e : aexp) : list sinstr :=

最後に、\ ``compile``\ 関数が正しく振る舞うことを述べている以下の定理を証明しなさい。まずは使える帰納法の仮定を得るため、より一般的な補題を述べる必要があるでしょう。

::

    Admitted.

☐
