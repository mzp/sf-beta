PE\_J: 部分評価
===============

Equiv\_J.v
ではプログラム変換の例として定数畳み込みを紹介し、そして、それがプログラムの意味を保存することを証明しました。定数畳み込みは\ ``ANum``\ 式のようなマニフェスト定数(リテラル)を処理します。例えば、コマンド\ ``Y ::= APlus (ANum 3) (ANum 1)``\ をコマンド\ ``Y ::= ANum 4``\ に単純化します。しかしながら、この操作は、定数とわかったことをデータフローに沿って伝播することは行いません。例えば、次の列

::

            X ::= ANum 3; Y ::= APlus (AId X) (ANum 1)

を

::

            X ::= ANum 3; Y ::= ANum 4

に単純化することはありません。なぜなら、\ ``X``\ が\ ``3``\ であったことは、\ ``Y``\ に渡された時には忘れられてしまうからです。

定数畳み込みを強化して、定数と分かったことを伝播し、それを使ってプログラムを単純化するようにしたいと思うのは自然なことです。そうすることは、部分評価(*partial
evaluation*)の初歩的な形となります。これから見るように、これを部分評価と呼ぶのは、プログラムを走らせることと似ているからです。ただ違うのは、プログラムの一部だけが評価されることです。その理由はプログラムの入力の一部だけがわかっているからです。例えば、\ ``Y``\ の初期値がわからないとき、プログラム

::

            X ::= ANum 3; Y ::= AMinus (APlus (AId X) (ANum 1)) (AId Y)

を単純化できるのは

::

            X ::= ANum 3; Y ::= AMinus (ANum 4) (AId Y)

までです。

::

    Require Export Imp_J.
    Require Import FunctionalExtensionality.

定数畳み込みを一般化する
------------------------

部分評価について最初にやることは、状態についての部分知識を表現することです。例えば上述の2つの代入において、部分評価器は\ ``X``\ が\ ``3``\ であることだけを知っており、他の変数については何も知らないでしょう。

部分状態
~~~~~~~~

概念的には、(完全な具体的状態の型が\ ``id -> nat``\ であるのに対して)部分状態は型\ ``id -> option nat``\ と考えることができます。しかしながら、部分状態の個別の変数の状態を参照/更新するだけでなく、条件分岐の制御フローを扱うために、2つの部分状態を比較して、同じかどうか、あるいは違いはどこかを知りたいことがあるでしょう。2つの任意の関数をこのように比較することはできません。このため、部分状態をより具体的な形、つまり\ ``id * nat``\ 対のリストとして表現します。

::

    Definition pe_state := list (id * nat).

これは、変数\ ``id``\ がこのリストに現れることが、その変数の現在の\ ``nat``\ 値を知っていることとするというアイデアです。そして\ ``pe_lookup``\ 関数はこの具体的表現を解釈します。(もし同じ変数\ ``id``\ がこのリストに複数回現れるならば、最初の出現が有効です。ただ、部分評価器はそのような\ ``pe_state``\ を構成することがないように定義します。)

::

    Fixpoint pe_lookup (pe_st : pe_state) (V:id) : option nat :=
      match pe_st with
      | [] => None
      | (V',n')::pe_st => if beq_id V V' then Some n'
                          else pe_lookup pe_st V
      end.

例えば、\ ``empty_pe_state``\ はすべての変数を完全に無視することを表します。すべての\ ``id``\ を\ ``None``\ に写像する関数です。

::

    Definition empty_pe_state : pe_state := [].

より一般に、もし\ ``pe_state``\ を表現する\ ``list``\ が、ある\ ``id``\ を含まないならば、\ ``pe_state``\ は\ ``id``\ を\ ``None``\ に写像しなければなりません。この事実を証明する前に、まず\ ``id``\ の等号関係の推論に関する便利なタクティックを定義します。タクティック

::

            compare V V' SCase

は\ ``beq_id V V'``\ が\ ``true``\ か\ ``false``\ かで場合分けする推論をすることを意味します。\ ``beq_id V V' = true``\ の場合、このタクティックは一貫して\ ``V``\ を\ ``V'``\ に置換します。

::

    Tactic Notation "compare" ident(i) ident(j) ident(c) :=
      let H := fresh "Heq" i j in
      destruct (beq_id i j) as [|]_eqn:H;
      [ Case_aux c "equal"; symmetry in H; apply beq_id_eq in H; subst j
      | Case_aux c "not equal" ].

    Theorem pe_domain: forall pe_st V n,
      pe_lookup pe_st V = Some n ->
      true = existsb (beq_id V) (map (@fst _ _) pe_st).
    Proof. intros pe_st V n H. induction pe_st as [| [V' n'] pe_st].
      Case "[]". inversion H.
      Case "::". simpl in H. simpl. compare V V' SCase; auto. Qed.

算術式
~~~~~~

``aexp``\ の部分評価は簡単です。基本的には定数畳み込み\ ``fold_constants_aexp``\ と同じです。違うのは、部分状態が変数の現在の値を教えてくれる場合があるので、その時に変数を定数式に置換できるということです。

::

    Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
      match a with
      | ANum n => ANum n
      | AId i => match pe_lookup pe_st i with

この部分評価器は定数を畳み込みしますが、可算の結合性の処理はしません。

::

    Example test_pe_aexp1:
      pe_aexp [(X,3)] (APlus (APlus (AId X) (ANum 1)) (AId Y))
      = APlus (ANum 4) (AId Y).
    Proof. reflexivity. Qed.

    Example text_pe_aexp2:
      pe_aexp [(Y,3)] (APlus (APlus (AId X) (ANum 1)) (AId Y))
      = APlus (APlus (AId X) (ANum 1)) (ANum 3).
    Proof. reflexivity. Qed.

さて、\ ``pe_aexp``\ はどういう意味で正しいのでしょうか？\ ``pe_aexp``\ の正しさを次のように定義するのが合理的です。完全状態\ ``st:state``\ が部分状態\ ``pe_st:pe_state``\ と整合的(*consistent*)であるならば(言い換えると、\ ``pe_st``\ で値が与えられていないすべての変数に\ ``st``\ と同じ値を代入した場合)常に、\ ``st``\ のもとでの\ ``a``\ の評価と\ ``pe_aexp pe_st a``\ の評価が同じ結果になる、ということです。この主張は実際に真です。

::

    Definition pe_consistent (st:state) (pe_st:pe_state) :=
      forall V n, Some n = pe_lookup pe_st V -> st V = n.

    Theorem pe_aexp_correct_weak: forall st pe_st, pe_consistent st pe_st ->
      forall a, aeval st a = aeval st (pe_aexp pe_st a).
    Proof. unfold pe_consistent. intros st pe_st H a.
      aexp_cases (induction a) Case; simpl;
        try reflexivity;
        try (destruct (pe_aexp pe_st a1);
             destruct (pe_aexp pe_st a2);
             rewrite IHa1; rewrite IHa2; reflexivity).

しかしながらすぐに、部分評価器で代入を削除することも行ないたくなるでしょう。例えば、

::

            X ::= ANum 3; Y ::= AMinus (AId X) (AId Y); X ::= ANum 4

を簡単化するには、\ ``X``\ の代入を最後に遅らせることで、単に

::

            Y ::= AMinus (ANum 3) (AId Y); X ::= ANum 4

となります。この単純化を達成するためには、

::

            pe_aexp [(X,3)] (AMinus (AId X) (AId Y))

を部分評価した結果は\ ``AMinus (ANum 3) (AId Y)``\ であるべきで、オリジナルの式\ ``AMinus (AId X) (AId Y)``\ ではありません。何といっても、

::

            X ::= ANum 3; Y ::= AMinus (AId X) (AId Y); X ::= ANum 4

を

::

            Y ::= AMinus (AId X) (AId Y); X ::= ANum 4

に変換することは、非効率であるだけではなく、間違っています。出力式\ ``AMinus (ANum 3) (AId Y)``\ と\ ``AMinus (AId X) (AId Y)``\ は両方とも正しさの基準を満たすにもかかわらずです。実のところ、単に\ ``pe_aexp pe_st a = a``\ と定義したとしても、定理\ ``pe_aexp_correct'``\ は成立してしまいます。

その代わりに、\ ``pe_aexp``\ がより強い意味で正しいことを証明します。つまり、部分評価によって生成された式を評価したもの(``aeval st (pe_aexp pe_st a)``)は、完全状態\ ``st``\ の、部分状態\ ``pe_st``\ によって特定された部分に依存しない、という意味でです。より正確にするために、関数\ ``pe_override``\ を、\ ``st``\ を\ ``pe_st``\ の内容に更新するものとして定義します。言い換えると、\ ``pe_override``\ は\ ``st``\ より優先して\ ``pe_st``\ にリストアップされた代入を行うということです。

::

    Fixpoint pe_override (st:state) (pe_st:pe_state) : state :=
      match pe_st with
      | [] => st
      | (V,n)::pe_st => update (pe_override st pe_st) V n
      end.

    Example test_pe_override:
      pe_override (update empty_state Y 1) [(X,3),(Z,2)]
      = update (update (update empty_state Y 1) Z 2) X 3.
    Proof. reflexivity. Qed.

``pe_override``\ が\ ``pe_state``\ を表現する具体的\ ``list``\ を操作するにもかかわらず、そのふるまいは\ ``pe_state``\ の\ ``pe_lookup``\ 解釈によって完全に定義されます。

::

    Theorem pe_override_correct: forall st pe_st V0,
      pe_override st pe_st V0 =
      match pe_lookup pe_st V0 with
      | Some n => n
      | None => st V0
      end.
    Proof. intros. induction pe_st as [| [V n] pe_st]. reflexivity.
      simpl in *. unfold update. rewrite beq_id_sym.
      compare V0 V Case; auto. Qed.

``pe_consistent``\ と\ ``pe_override``\ とは2つの方法で関係付けることができます。1つ目は、状態を部分状態でオーバーライド(上書き)したものは、常にその部分状態と整合的な状態となるということです。2つ目は、状態がもし部分状態と整合的ならば、その状態をその部分状態でオーバーライドしたものは、もとの状態と同じということです。

::

    Theorem pe_override_consistent: forall st pe_st,
      pe_consistent (pe_override st pe_st) pe_st.
    Proof. intros st pe_st V n H. rewrite pe_override_correct.
      destruct (pe_lookup pe_st V); inversion H. reflexivity. Qed.

    Theorem pe_consistent_override: forall st pe_st,
      pe_consistent st pe_st -> forall V, st V = pe_override st pe_st V.
    Proof. intros st pe_st H V. rewrite pe_override_correct.
      remember (pe_lookup pe_st V) as l. destruct l; auto. Qed.

いよいよ、\ ``pe_aexp``\ がより強い意味で正しいことを主張し証明します。このことはこれから部分評価器の残りを定義する助けになります。

直観的には、部分評価を使ったプログラムの実行は2つのステージから成る過程です。第一の「静的」ステージでは、与えられたプログラムをある部分状態のもとで部分評価し、「残留」プログラムを得ます。第二の「動的」ステージは、残留プログラムを残りの状態で評価します。この動的ステージでは、静的(部分)状態ではわからなかった変数の値が与えられます。したがって残留プログラムは、部分状態にリストアップされた代入をもとのプログラムの前に追加したものと同値になります。

::

    Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
      aeval (pe_override st pe_st) a = aeval st (pe_aexp pe_st a).
    Proof.
      intros pe_st a st.
      aexp_cases (induction a) Case; simpl;
        try reflexivity;
        try (destruct (pe_aexp pe_st a1);
             destruct (pe_aexp pe_st a2);
             rewrite IHa1; rewrite IHa2; reflexivity).

ブール式
~~~~~~~~

ブール式の部分評価は同様です。実のところ、ブール式の定数畳み込みと完全に対応します。なぜなら、この言語にはブール値の変数がないからです。

::

    Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
      match b with
      | BTrue        => BTrue
      | BFalse       => BFalse
      | BEq a1 a2 =>
          match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
          | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
          | (a1', a2') => BEq a1' a2'
          end
      | BLe a1 a2 =>
          match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
          | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
          | (a1', a2') => BLe a1' a2'
          end
      | BNot b1 =>
          match (pe_bexp pe_st b1) with
          | BTrue => BFalse
          | BFalse => BTrue
          | b1' => BNot b1'
          end
      | BAnd b1 b2 =>
          match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
          | (BTrue, BTrue) => BTrue
          | (BTrue, BFalse) => BFalse
          | (BFalse, BTrue) => BFalse
          | (BFalse, BFalse) => BFalse
          | (b1', b2') => BAnd b1' b2'
          end
      end.

    Example test_pe_bexp1:
      pe_bexp [(X,3)] (BNot (BLe (AId X) (ANum 3)))
      = BFalse.
    Proof. reflexivity. Qed.

    Example test_pe_bexp2: forall b,
      b = BNot (BLe (AId X) (APlus (AId X) (ANum 1))) ->
      pe_bexp [] b = b.
    Proof. intros b H. rewrite -> H. reflexivity. Qed.

``pe_bexp``\ の正しさは上述の\ ``pe_aexp``\ の正しさと同様です。

::

    Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
      beval (pe_override st pe_st) b = beval st (pe_bexp pe_st b).
    Proof.
      intros pe_st b st.
      bexp_cases (induction b) Case; simpl;
        try reflexivity;
        try (remember (pe_aexp pe_st a) as a';
             remember (pe_aexp pe_st a0) as a0';
             assert (Ha: aeval (pe_override st pe_st) a = aeval st a');
             assert (Ha0: aeval (pe_override st pe_st) a0 = aeval st a0');
               try (subst; apply pe_aexp_correct);
             destruct a'; destruct a0'; rewrite Ha; rewrite Ha0;
             simpl; try destruct (beq_nat n n0); try destruct (ble_nat n n0);
             reflexivity);
        try (destruct (pe_bexp pe_st b); rewrite IHb; reflexivity);
        try (destruct (pe_bexp pe_st b1);
             destruct (pe_bexp pe_st b2);
             rewrite IHb1; rewrite IHb2; reflexivity).
    Qed.

ループ以外のコマンドの部分評価
------------------------------

コマンドの部分評価はどうなるでしょうか？部分評価と完全評価の対応関係は続きます。コマンドの完全評価が初期状態を終了状態に変換するのと同じように、コマンドの部分評価は初期部分状態を終了部分状態に変換します。違いは、状態が完全ではないことから、コマンドのある部分が静的ステージでは実行可能でない可能性があることです。上記の\ ``pe_aexp``\ が残留\ ``aexp``\ を返し、\ ``pe_bexp``\ が残留\ ``bexp``\ を返すように、コマンドを部分評価すると残留コマンドとなります。

部分評価器が完全評価器と似ている別の点は、すべてのコマンドに対して停止するとは限らないということです。すべてのコマンドに対して停止する部分評価器を構築することは難しくはありません。難しいのは、すべてのコマンドに対して停止し、かつ、ループの展開のような最適化を自動的に行う部分評価器を構築することです。しばしば、ソースプログラムの書き方を変えて、静的情報と動的情報の区別をより明確にしてやることで、部分評価器がより多くの場合に停止し、より良い最適化をしてくれるように誘導することができます。そのような誘導は「束縛時改良術」(the
art of *binding-time
improvement*)です。変数の束縛の時が、その値が「静的」("static")か「動的」("dynamic")かがわかる時です。

とにかく、今のところは、対象とする部分評価器は、ソースコマンドと初期部分状態から残留コマンドと最終部分状態への全関数ではない、という事実を受け入れておきます。この非停止性をモデル化するため、コマンドの完全評価と同様、帰納的に定義された関係を使います。次の記述:

::

            c1 / st || c1' / st'

は、ソースコマンド\ ``c1``\ を初期部分状態\ ``st``\ のもとで部分評価すると、残留コマンド\ ``c1'``\ と最終部分状態\ ``st'``\ になることを意味します。例えば、次のようなことが成立することを期待するでしょう:

::

            (X ::= ANum 3 ; Y ::= AMult (AId Z) (APlus (AId X) (AId X)))
            / [] || (Y ::= AMult (AId Z) (ANum 6)) / [(X,3)]

``X``\ への代入は残留コマンドではなく、最終部分状態に現れます。

代入
~~~~

代入がどのように部分評価されるかを考えることから始めましょう。上述のソースプログラムにおける2つの代入は、違った形で扱う必要があります。最初の代入\ ``X ::= ANum 3``\ は「静的」です。その右辺は定数(より一般には定数に簡単化されるもの)です。これから部分状態の\ ``X``\ を\ ``3``\ に更新し、残留コードは生成しません。(実際には、残留コードとして\ ``SKIP``\ を作ります。)2つ目の代入\ ``Y ::= AMult (AId Z) (APlus (AId X) (AId X))``\ は「動的」です。右辺は定数に単純化されることはありません。これから、この代入は残留コードに残され、\ ``Y``\ がもし部分状態に存在していたなら、その\ ``Y``\ が除去されます。この2つの場合を実装するために、関数\ ``pe_add``\ と\ ``pe_remove``\ を定義します。上述の\ ``pe_override``\ のように、これらの関数は\ ``pe_state``\ を表現する具体的な\ ``list``\ を操作しますが、定理\ ``pe_add_correct``\ と\ ``pe_remove_correct``\ はこれらの関数のふるまいを\ ``pe_state``\ の\ ``pe_lookup``\ による解釈にもとづいて規定します。

::

    Fixpoint pe_remove (pe_st:pe_state) (V:id) : pe_state :=
      match pe_st with
      | [] => []
      | (V',n')::pe_st => if beq_id V V' then pe_remove pe_st V
                          else (V',n') :: pe_remove pe_st V
      end.

    Theorem pe_remove_correct: forall pe_st V V0,
      pe_lookup (pe_remove pe_st V) V0
      = if beq_id V V0 then None else pe_lookup pe_st V0.
    Proof. intros pe_st V V0. induction pe_st as [| [V' n'] pe_st].
      Case "[]". destruct (beq_id V V0); reflexivity.
      Case "::". simpl. compare V V' SCase.
        SCase "equal". rewrite IHpe_st.
          replace (beq_id V0 V) with (beq_id V V0) by apply beq_id_sym.
          destruct (beq_id V V0); reflexivity.
        SCase "not equal". simpl. compare V0 V' SSCase.
          SSCase "equal". rewrite HeqVV'. reflexivity.
          SSCase "not equal". rewrite IHpe_st. reflexivity.
    Qed.

    Definition pe_add (pe_st:pe_state) (V:id) (n:nat) : pe_state :=
      (V,n) :: pe_remove pe_st V.

    Theorem pe_add_correct: forall pe_st V n V0,
      pe_lookup (pe_add pe_st V n) V0
      = if beq_id V V0 then Some n else pe_lookup pe_st V0.
    Proof. intros pe_st V n V0. unfold pe_add. simpl. rewrite beq_id_sym.
      compare V V0 Case.
      Case "equal". reflexivity.
      Case "not equal". rewrite pe_remove_correct. rewrite HeqVV0. reflexivity.
    Qed.

以下の2つ定理は、定義する部分評価器が動的代入と静的代入をそれぞれ正しく扱うことを示すのに使われます。

::

    Theorem pe_override_update_remove: forall st pe_st V n,
      update (pe_override st pe_st) V n =
      pe_override (update st V n) (pe_remove pe_st V).
    Proof. intros st pe_st V n. apply functional_extensionality. intros V0.
      unfold update. rewrite !pe_override_correct. rewrite pe_remove_correct.
      destruct (beq_id V V0); reflexivity. Qed.

    Theorem pe_override_update_add: forall st pe_st V n,
      update (pe_override st pe_st) V n =
      pe_override st (pe_add pe_st V n).
    Proof. intros st pe_st V n. apply functional_extensionality. intros V0.
      unfold update. rewrite !pe_override_correct. rewrite pe_add_correct.
      destruct (beq_id V V0); reflexivity. Qed.

条件分岐
~~~~~~~~

部分評価について代入よりトリッキーなのは条件分岐\ ``IFB b1 THEN c1 ELSE c2 FI``\ です。もし\ ``b1``\ が\ ``BTrue``\ または\ ``BFalse``\ に単純化されるならば、簡単です。どちらの選択肢が選ばれるか分かっているのですから、その選択肢を考えるだけです。もし\ ``b1``\ が定数に単純化されないならば、両方の選択肢を考える必要があります。そして、最終部分状態は2つの選択肢で違うかもしれません!

次のプログラムは、問題の難しさを表します:

::

            X ::= ANum 3;
            IFB BLe (AId Y) (ANum 4) THEN
                Y ::= ANum 4;
                IFB BEq (AId X) (AId Y) THEN Y ::= ANum 999 ELSE SKIP FI
            ELSE SKIP FI

初期部分状態が空とします。静的に\ ``Y``\ を\ ``4``\ と比較する方法を知りません。これから、(外側の)条件分岐の両方の選択肢を部分評価しなければなりません。\ ``THEN``\ の側では、\ ``Y``\ が\ ``4``\ になり、コードを単純化する知識をいくらか使うことができるでしょう。\ ``ELSE``\ の側では最後の段階で未だに\ ``Y``\ の値が確定しません。最終部分状態と残留プログラムはどうなるべきでしょうか？

このような動的条件分岐を扱う一つの方法は、2つの選択肢の最終部分状態の共通部分をとるというものです。この例では、\ ``(Y,4),(X,3)``\ と\ ``(X,3)``\ の共通部分をとります。従って、全体の最終部分状態は\ ``(X,3)``\ です。\ ``Y``\ が\ ``4``\ であるという情報を失なった代償として、\ ``THEN``\ 選択肢の最後に代入\ ``Y ::= ANum 4``\ を追加する必要があります。結局、残留プログラムは次のようなものになります:

::

            SKIP;
            IFB BLe (AId Y) (ANum 4) THEN
                SKIP;
                SKIP;
                Y ::= ANum 4
            ELSE SKIP FI

Coqでこの場合をプログラミングするには、いくつものさらなる関数が必要です。2つの\ ``pe_state``\ の共通部分を計算する必要があります。また、2つの\ ``pe_state``\ の違いを代入に変換する必要もあります。

最初に、2つの\ ``pe_state``\ が特定の変数について不一致かどうかを計算する方法を示します。定理\ ``pe_disagree_domain``\ において、2つの\ ``pe_state``\ が変数について不一致になるのは、少なくとも一方にその変数が現れるときだけであることを証明します。

::

    Definition pe_disagree_at (pe_st1 pe_st2 : pe_state) (V:id) : bool :=
      match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
      | Some x, Some y => negb (beq_nat x y)
      | None, None => false
      | _, _ => true
      end.

    Lemma existsb_app: forall X (f:X->bool) l1 l2,
      existsb f (l1 ++ l2) = orb (existsb f l1) (existsb f l2).
    Proof. intros X f l1 l2. induction l1. reflexivity.
      simpl. rewrite IHl1. rewrite orb_assoc. reflexivity. Qed.

    Theorem pe_disagree_domain: forall (pe_st1 pe_st2 : pe_state) (V:id),
      true = pe_disagree_at pe_st1 pe_st2 V ->
      true = existsb (beq_id V) (map (@fst _ _) pe_st1 ++
                                 map (@fst _ _) pe_st2).
    Proof. unfold pe_disagree_at. intros pe_st1 pe_st2 V H.
      rewrite existsb_app. symmetry. apply orb_true_intro.
      remember (pe_lookup pe_st1 V) as lookup1.
      destruct lookup1 as [n1|]. left. symmetry. apply pe_domain with n1. auto.
      remember (pe_lookup pe_st2 V) as lookup2.
      destruct lookup2 as [n2|]. right. symmetry. apply pe_domain with n2. auto.
      inversion H. Qed.

2つの与えられた\ ``pe_state``\ の不一致の変数をリストアップする関数\ ``pe_compare``\ を定義します。このリストはまさに、定理\ ``pe_compare_correct``\ に従うならば、このリストにある変数が現れることと、与えられた2つの\ ``pe_state``\ がその変数で不一致であることが同値である、というものです。さらに、リストから重複を除去するために\ ``pe_unique``\ 関数を使います。

::

    Fixpoint pe_unique (l : list id) : list id :=
      match l with
      | [] => []
      | x::l => x :: filter (fun y => negb (beq_id x y)) (pe_unique l)
      end.

    Lemma existsb_beq_id_filter: forall V f l,
      existsb (beq_id V) (filter f l) = andb (existsb (beq_id V) l) (f V).
    Proof. intros V f l. induction l as [| h l].
      Case "[]". reflexivity.
      Case "h::l". simpl. remember (f h) as fh. destruct fh.
        SCase "true = f h". simpl. rewrite IHl. compare V h SSCase.
          rewrite <- Heqfh. reflexivity. reflexivity.
        SCase "false = f h". rewrite IHl. compare V h SSCase.
          rewrite <- Heqfh. rewrite !andb_false_r. reflexivity. reflexivity.
    Qed.

    Theorem pe_unique_correct: forall l x,
      existsb (beq_id x) l = existsb (beq_id x) (pe_unique l).
    Proof. intros l x. induction l as [| h t]. reflexivity.
      simpl in *. compare x h Case.
      Case "equal". reflexivity.
      Case "not equal".
        rewrite -> existsb_beq_id_filter, <- IHt, -> beq_id_sym, -> Heqxh,
                -> andb_true_r. reflexivity. Qed.

    Definition pe_compare (pe_st1 pe_st2 : pe_state) : list id :=
      pe_unique (filter (pe_disagree_at pe_st1 pe_st2)
        (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2)).

    Theorem pe_compare_correct: forall pe_st1 pe_st2 V,
      pe_lookup pe_st1 V = pe_lookup pe_st2 V <->
      false = existsb (beq_id V) (pe_compare pe_st1 pe_st2).
    Proof. intros pe_st1 pe_st2 V.
      unfold pe_compare. rewrite <- pe_unique_correct, -> existsb_beq_id_filter.
      split; intros Heq.
      Case "->".
        symmetry. apply andb_false_intro2. unfold pe_disagree_at. rewrite Heq.
        destruct (pe_lookup pe_st2 V).
        rewrite <- beq_nat_refl. reflexivity.
        reflexivity.
      Case "<-".
        assert (Hagree: pe_disagree_at pe_st1 pe_st2 V = false).
          SCase "Proof of assertion".
          remember (pe_disagree_at pe_st1 pe_st2 V) as disagree.
          destruct disagree; [| reflexivity].
          rewrite -> andb_true_r, <- pe_disagree_domain in Heq.
          inversion Heq.
          apply Heqdisagree.
        unfold pe_disagree_at in Hagree.
        destruct (pe_lookup pe_st1 V) as [n1|];
        destruct (pe_lookup pe_st2 V) as [n2|];
          try reflexivity; try solve by inversion.
        rewrite beq_nat_eq with n1 n2. reflexivity.
        rewrite <- negb_involutive. rewrite Hagree. reflexivity. Qed.

2つの部分状態の共通部分は、どちらか一方から、不一致の変数のすべてを除去したものです。このような変数のリスト全体の除去を一度に行う関数\ ``pe_removes``\ を、上述の\ ``pe_remove``\ を使って定義します。

定理\ ``pe_compare_removes``\ は、共通部分をとる操作の結果の\ ``pe_lookup``\ による解釈が、変数を除去する元として2つの部分状態のどちらを使っても同じであることを述べます。\ ``pe_override``\ は部分状態の\ ``pe_lookup``\ による解釈だけに依存していることから、\ ``pe_override``\ もまた2つの部分状態のどちらから変数を除去するかに関係ないことが言えます。定理\ ``pe_compare_override``\ は正しさの証明の中で簡単に使われます。

::

    Fixpoint pe_removes (pe_st:pe_state) (ids : list id) : pe_state :=
      match ids with
      | [] => pe_st
      | V::ids => pe_remove (pe_removes pe_st ids) V
      end.

    Theorem pe_removes_correct: forall pe_st ids V,
      pe_lookup (pe_removes pe_st ids) V =
      if existsb (beq_id V) ids then None else pe_lookup pe_st V.
    Proof. intros pe_st ids V. induction ids as [| V' ids]. reflexivity.
      simpl. rewrite pe_remove_correct. rewrite IHids.
      replace (beq_id V' V) with (beq_id V V') by apply beq_id_sym.
      destruct (beq_id V V'); destruct (existsb (beq_id V) ids); reflexivity.
    Qed.

    Theorem pe_compare_removes: forall pe_st1 pe_st2 V,
      pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
      pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V.
    Proof. intros pe_st1 pe_st2 V. rewrite !pe_removes_correct.
      remember (existsb (beq_id V) (pe_compare pe_st1 pe_st2)) as b.
      destruct b. reflexivity.
      apply pe_compare_correct in Heqb. apply Heqb. Qed.

    Theorem pe_compare_override: forall pe_st1 pe_st2 st,
      pe_override st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
      pe_override st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)).
    Proof. intros. apply functional_extensionality. intros V.
      rewrite !pe_override_correct. rewrite pe_compare_removes. reflexivity.
    Qed.

最後に、2つの部分状態の違いを代入コマンドの列に変換する\ ``assign``\ 関数を定義します。より詳しくは、\ ``assign pe_st ids``\ は、\ ``ids``\ にリストアップされたそれぞれの変数に対して代入コマンドを生成します。

::

    Fixpoint assign (pe_st : pe_state) (ids : list id) : com :=
      match ids with
      | [] => SKIP
      | V::ids => match pe_lookup pe_st V with
                  | Some n => (assign pe_st ids; V ::= ANum n)
                  | None => assign pe_st ids
                  end
      end.

``assign``\ により生成されたコマンドは常に停止します。なぜなら、単に代入の列だからです。下記の(全)関数\ ``assigned``\ はコマンドの(動的状態での)効果を計算します。そして定理\ ``assign_removes``\ は、生成された代入の列が部分状態からの変数の除去を完全に補償することを保証します。

::

    Definition assigned (pe_st:pe_state) (ids : list id) (st:state) : state :=
      fun V => match existsb (beq_id V) ids, pe_lookup pe_st V with
               | true, Some n => n
               | _, _ => st V
               end.

    Theorem assign_removes: forall pe_st ids st,
      pe_override st pe_st =
      pe_override (assigned pe_st ids st) (pe_removes pe_st ids).
    Proof. intros pe_st ids st. apply functional_extensionality. intros V.
      rewrite !pe_override_correct. rewrite pe_removes_correct. unfold assigned.
      destruct (existsb (beq_id V)); destruct (pe_lookup pe_st V); reflexivity.
    Qed.

    Lemma ceval_extensionality: forall c st st1 st2,
      c / st || st1 -> (forall V, st1 V = st2 V) -> c / st || st2.
    Proof. intros c st st1 st2 H Heq.
      apply functional_extensionality in Heq. rewrite <- Heq. apply H. Qed.

    Theorem eval_assign: forall pe_st ids st,
      assign pe_st ids / st || assigned pe_st ids st.
    Proof. intros pe_st ids st. induction ids as [| V ids]; simpl.
      Case "[]". eapply ceval_extensionality. apply E_Skip. reflexivity.
      Case "V::ids".
        remember (pe_lookup pe_st V) as lookup. destruct lookup.
        SCase "Some". eapply E_Seq. apply IHids. unfold assigned. simpl.
          eapply ceval_extensionality. apply E_Ass. simpl. reflexivity.
          intros V0. unfold update. rewrite beq_id_sym. compare V0 V SSCase.
          SSCase "equal". rewrite <- Heqlookup. reflexivity.
          SSCase "not equal". reflexivity.
        SCase "None". eapply ceval_extensionality. apply IHids.
          unfold assigned. intros V0. simpl. compare V0 V SSCase.
          SSCase "equal". rewrite <- Heqlookup.
            destruct (existsb (beq_id V0) ids); reflexivity.
          SSCase "not equal". reflexivity. Qed.

部分評価関係
~~~~~~~~~~~~

遂に、ループ以外のコマンドに対する部分評価器を、帰納的関係として定義することができます!\ ``PE_AssDynamic``\ と\ ``PE_If``\ における非等号(``<>``)条件は、部分評価器に決定性を持たせるためのものです。これらは正しさのためには必要ありません。

::

    Reserved Notation "c1 '/' st '||' c1' '/' st'"
      (at level 40, st at level 39, c1' at level 39).

    Inductive pe_com : com -> pe_state -> com -> pe_state -> Prop :=
      | PE_Skip : forall pe_st,
          SKIP / pe_st || SKIP / pe_st
      | PE_AssStatic : forall pe_st a1 n1 l,
          pe_aexp pe_st a1 = ANum n1 ->
          (l ::= a1) / pe_st || SKIP / pe_add pe_st l n1
      | PE_AssDynamic : forall pe_st a1 a1' l,
          pe_aexp pe_st a1 = a1' ->
          (forall n, a1' <> ANum n) ->
          (l ::= a1) / pe_st || (l ::= a1') / pe_remove pe_st l
      | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2',
          c1 / pe_st  || c1' / pe_st' ->
          c2 / pe_st' || c2' / pe_st'' ->
          (c1 ; c2) / pe_st || (c1' ; c2') / pe_st''
      | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1',
          pe_bexp pe_st b1 = BTrue ->
          c1 / pe_st || c1' / pe_st' ->
          (IFB b1 THEN c1 ELSE c2 FI) / pe_st || c1' / pe_st'
      | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2',
          pe_bexp pe_st b1 = BFalse ->
          c2 / pe_st || c2' / pe_st' ->
          (IFB b1 THEN c1 ELSE c2 FI) / pe_st || c2' / pe_st'
      | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
          pe_bexp pe_st b1 <> BTrue ->
          pe_bexp pe_st b1 <> BFalse ->
          c1 / pe_st || c1' / pe_st1 ->
          c2 / pe_st || c2' / pe_st2 ->
          (IFB b1 THEN c1 ELSE c2 FI) / pe_st
            || (IFB pe_bexp pe_st b1
                 THEN c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
                 ELSE c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) FI)
                / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)

      where "c1 '/' st '||' c1' '/' st'" := (pe_com c1 st c1' st').

    Tactic Notation "pe_com_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "PE_Skip"
      | Case_aux c "PE_AssStatic" | Case_aux c "PE_AssDynamic"
      | Case_aux c "PE_Seq"
      | Case_aux c "PE_IfTrue" | Case_aux c "PE_IfFalse" | Case_aux c "PE_If" ].

    Hint Constructors pe_com.
    Hint Constructors ceval.

例
~~

以下は部分評価器を利用する例のいくつかです。\ ``pe_com``\ 関係を自動部分評価に実際に利用可能にするためには、Coqにより多くの自動化タクティックを定義する必要があるでしょう。それは難しいことではありませんが、ここでは必要ありません。

::

    Example pe_example1:
      (X ::= ANum 3 ; Y ::= AMult (AId Z) (APlus (AId X) (AId X)))
      / [] || (SKIP; Y ::= AMult (AId Z) (ANum 6)) / [(X,3)].
    Proof. eapply PE_Seq. eapply PE_AssStatic. reflexivity.
      eapply PE_AssDynamic. reflexivity. intros n H. inversion H. Qed.

    Example pe_example2:
      (X ::= ANum 3 ; IFB BLe (AId X) (ANum 4) THEN X ::= ANum 4 ELSE SKIP FI)
      / [] || (SKIP; SKIP) / [(X,4)].
    Proof. eapply PE_Seq. eapply PE_AssStatic. reflexivity.
      eapply PE_IfTrue. reflexivity.
      eapply PE_AssStatic. reflexivity. Qed.

    Example pe_example3:
      (X ::= ANum 3;
       IFB BLe (AId Y) (ANum 4) THEN
         Y ::= ANum 4;
         IFB BEq (AId X) (AId Y) THEN Y ::= ANum 999 ELSE SKIP FI
       ELSE SKIP FI) / []
      || (SKIP;
           IFB BLe (AId Y) (ANum 4) THEN
             (SKIP; SKIP); (SKIP; Y ::= ANum 4)
           ELSE SKIP; SKIP FI)
          / [(X,3)].
    Proof. erewrite f_equal2 with (f := fun c st => _ / _ || c / st).
      eapply PE_Seq. eapply PE_AssStatic. reflexivity.
      eapply PE_If; intuition eauto; try solve by inversion.
      econstructor. eapply PE_AssStatic. reflexivity.
      eapply PE_IfFalse. reflexivity. econstructor.
      reflexivity. reflexivity. Qed.

部分評価の正しさ
~~~~~~~~~~~~~~~~

最後に、定義した部分評価器が正しいことを証明しましょう!

::

    Reserved Notation "c' '/' pe_st' '/' st '||' st''"
      (at level 40, pe_st' at level 39, st at level 39).

    Inductive pe_ceval
      (c':com) (pe_st':pe_state) (st:state) (st'':state) : Prop :=
      | pe_ceval_intro : forall st',
        c' / st || st' ->
        pe_override st' pe_st' = st'' ->
        c' / pe_st' / st || st''
      where "c' '/' pe_st' '/' st '||' st''" := (pe_ceval c' pe_st' st st'').

    Hint Constructors pe_ceval.

    Theorem pe_com_complete:
      forall c pe_st pe_st' c', c / pe_st || c' / pe_st' ->
      forall st st'',
      (c / pe_override st pe_st || st'') ->
      (c' / pe_st' / st || st'').
    Proof. intros c pe_st pe_st' c' Hpe.
      pe_com_cases (induction Hpe) Case; intros st st'' Heval;
      try (inversion Heval; subst;
           try (rewrite -> pe_bexp_correct, -> H in *; solve by inversion);
           []);
      eauto.
      Case "PE_AssStatic". econstructor. econstructor.
        rewrite -> pe_aexp_correct. rewrite <- pe_override_update_add.
        rewrite -> H. reflexivity.
      Case "PE_AssDynamic". econstructor. econstructor. reflexivity.
        rewrite -> pe_aexp_correct. rewrite <- pe_override_update_remove.
        reflexivity.
      Case "PE_Seq".
        edestruct IHHpe1. eassumption. subst.
        edestruct IHHpe2. eassumption.
        eauto.
      Case "PE_If". inversion Heval; subst.
        SCase "E'IfTrue". edestruct IHHpe1. eassumption.
          econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
          eapply E_Seq. eassumption. apply eval_assign.
          rewrite <- assign_removes. eassumption.
        SCase "E_IfFalse". edestruct IHHpe2. eassumption.
          econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
          eapply E_Seq. eassumption. apply eval_assign.
          rewrite -> pe_compare_override.
          rewrite <- assign_removes. eassumption.
    Qed.

    Theorem pe_com_sound:
      forall c pe_st pe_st' c', c / pe_st || c' / pe_st' ->
      forall st st'',
      (c' / pe_st' / st || st'') ->
      (c / pe_override st pe_st || st'').
    Proof. intros c pe_st pe_st' c' Hpe.
      pe_com_cases (induction Hpe) Case;
        intros st st'' [st' Heval Heq];
        try (inversion Heval; []; subst); auto.
      Case "PE_AssStatic". rewrite <- pe_override_update_add. apply E_Ass.
        rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
      Case "PE_AssDynamic". rewrite <- pe_override_update_remove. apply E_Ass.
        rewrite <- pe_aexp_correct. reflexivity.
      Case "PE_Seq". eapply E_Seq; eauto.
      Case "PE_IfTrue". apply E_IfTrue.
        rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
      Case "PE_IfFalse". apply E_IfFalse.
        rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
      Case "PE_If".
        inversion Heval; subst; inversion H7;
          (eapply ceval_deterministic in H8; [| apply eval_assign]); subst.
        SCase "E_IfTrue".
          apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
          rewrite <- assign_removes. eauto.
        SCase "E_IfFalse".
          rewrite -> pe_compare_override.
          apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
          rewrite <- assign_removes. eauto.
    Qed.

メインの定理です。この形式化について David Menendez に感謝します!

::

    Corollary pe_com_correct:
      forall c pe_st pe_st' c', c / pe_st || c' / pe_st' ->
      forall st st'',
      (c / pe_override st pe_st || st'') <->
      (c' / pe_st' / st || st'').
    Proof. intros c pe_st pe_st' c' H st st''. split.
      Case "->". apply pe_com_complete. apply H.
      Case "<-". apply pe_com_sound. apply H.
    Qed.

ループの部分評価
----------------

一見すると、部分評価関係\ ``pe_com``\ をループに拡張することは簡単に見えます。実際、多くのループは扱うのは簡単です。例えば次の、二乗を繰り返すループを考えます:

::

            WHILE BLe (ANum 1) (AId X) DO
                Y ::= AMult (AId Y) (AId Y);
                X ::= AMinus (AId X) (ANum 1)
            END

``X``\ も\ ``Y``\ も静的には分からないとき、ループ全体が動的で、残留コマンドはループ全体と同じです。\ ``X``\ が分かり\ ``Y``\ が分からないときは、ループは完全に展開でき、もし\ ``X``\ が最初は\ ``3``\ (で最後は\ ``0``)だとすると、残留コマンドは

::

            Y ::= AMult (AId Y) (AId Y);
            Y ::= AMult (AId Y) (AId Y);
            Y ::= AMult (AId Y) (AId Y)

となります。一般にループは、ループ本体の最終部分状態が初期状態と同じである場合、または、ガード条件が静的である場合には、部分評価は簡単です。

しかし、Impには、残留プログラムを示すのが難しい別のループが存在します。例えば、\ ``Y``\ が偶数か奇数かをチェックする次のプログラムを考えます:

::

            X ::= ANum 0;
            WHILE BLe (ANum 1) (AId Y) DO
                Y ::= AMinus (AId Y) (ANum 1);
                X ::= AMinus (ANum 1) (AId X)
            END

``X``\ の値はループの間、\ ``0``\ と\ ``1``\ を交互にとります。理想的には、ループを完全にではなく2段階展開したいところです。次のような感じです:

::

            WHILE BLe (ANum 1) (AId Y) DO
                Y ::= AMinus (AId Y) (ANum 1);
                IF BLe (ANum 1) (AId Y) THEN
                    Y ::= AMinus (AId Y) (ANum 1)
                ELSE
                    X ::= ANum 1; EXIT
                FI
            END;
            X ::= ANum 0

残念ながら、Impには\ ``EXIT``\ コマンドはありません。言語の制御構造を拡張しない範囲では、できることは、ループのガードのテストを繰り返すか、フラグ変数を追加することです。どちらにしても、ひどいものです。

それでも、本筋から逸れますが、以下はImpコマンドに部分評価を行おうとする試みです。\ ``pe_com``\ 関係にもう1つコマンド引数\ ``c''``\ を追加して、展開するループを追跡します。

::

    Module Loop.

    Reserved Notation "c1 '/' st '||' c1' '/' st' '/' c''"
      (at level 40, st at level 39, c1' at level 39, st' at level 39).

    Inductive pe_com : com -> pe_state -> com -> pe_state -> com -> Prop :=
      | PE_Skip : forall pe_st,
          SKIP / pe_st || SKIP / pe_st / SKIP
      | PE_AssStatic : forall pe_st a1 n1 l,
          pe_aexp pe_st a1 = ANum n1 ->
          (l ::= a1) / pe_st || SKIP / pe_add pe_st l n1 / SKIP
      | PE_AssDynamic : forall pe_st a1 a1' l,
          pe_aexp pe_st a1 = a1' ->
          (forall n, a1' <> ANum n) ->
          (l ::= a1) / pe_st || (l ::= a1') / pe_remove pe_st l / SKIP
      | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
          c1 / pe_st  || c1' / pe_st' / SKIP ->
          c2 / pe_st' || c2' / pe_st'' / c'' ->
          (c1 ; c2) / pe_st || (c1' ; c2') / pe_st'' / c''
      | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1' c'',
          pe_bexp pe_st b1 = BTrue ->
          c1 / pe_st || c1' / pe_st' / c'' ->
          (IFB b1 THEN c1 ELSE c2 FI) / pe_st || c1' / pe_st' / c''
      | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2' c'',
          pe_bexp pe_st b1 = BFalse ->
          c2 / pe_st || c2' / pe_st' / c'' ->
          (IFB b1 THEN c1 ELSE c2 FI) / pe_st || c2' / pe_st' / c''
      | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
          pe_bexp pe_st b1 <> BTrue ->
          pe_bexp pe_st b1 <> BFalse ->
          c1 / pe_st || c1' / pe_st1 / c'' ->
          c2 / pe_st || c2' / pe_st2 / c'' ->
          (IFB b1 THEN c1 ELSE c2 FI) / pe_st
            || (IFB pe_bexp pe_st b1
                 THEN c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
                 ELSE c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) FI)
                / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)
                / c''
      | PE_WhileEnd : forall pe_st b1 c1,
          pe_bexp pe_st b1 = BFalse ->
          (WHILE b1 DO c1 END) / pe_st || SKIP / pe_st / SKIP
      | PE_WhileLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
          pe_bexp pe_st b1 = BTrue ->
          c1 / pe_st || c1' / pe_st' / SKIP ->
          (WHILE b1 DO c1 END) / pe_st' || c2' / pe_st'' / c2'' ->
          pe_compare pe_st pe_st'' <> [] ->
          (WHILE b1 DO c1 END) / pe_st || (c1';c2') / pe_st'' / c2''
      | PE_While : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
          pe_bexp pe_st b1 <> BFalse ->
          pe_bexp pe_st b1 <> BTrue ->
          c1 / pe_st || c1' / pe_st' / SKIP ->
          (WHILE b1 DO c1 END) / pe_st' || c2' / pe_st'' / c2'' ->
          pe_compare pe_st pe_st'' <> [] ->
          (c2'' = SKIP \/ c2'' = WHILE b1 DO c1 END) ->
          (WHILE b1 DO c1 END) / pe_st
            || (IFB pe_bexp pe_st b1
                 THEN c1'; c2'; assign pe_st'' (pe_compare pe_st pe_st'')
                 ELSE assign pe_st (pe_compare pe_st pe_st'') FI)
                / pe_removes pe_st (pe_compare pe_st pe_st'')
                / c2''
      | PE_WhileFixedEnd : forall pe_st b1 c1,
          pe_bexp pe_st b1 <> BFalse ->
          (WHILE b1 DO c1 END) / pe_st || SKIP / pe_st / (WHILE b1 DO c1 END)
      | PE_WhileFixedLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
          pe_bexp pe_st b1 = BTrue ->
          c1 / pe_st || c1' / pe_st' / SKIP ->
          (WHILE b1 DO c1 END) / pe_st'
            || c2' / pe_st'' / (WHILE b1 DO c1 END) ->
          pe_compare pe_st pe_st'' = [] ->
          (WHILE b1 DO c1 END) / pe_st
            || (WHILE BTrue DO SKIP END) / pe_st / SKIP

例
~~

::

    Tactic Notation "step" ident(i) :=
      (eapply i; intuition eauto; try solve by inversion);
      repeat (try eapply PE_Seq;
              try (eapply PE_AssStatic; simpl; reflexivity);
              try (eapply PE_AssDynamic;
                   [ simpl; reflexivity
                   | intuition eauto; solve by inversion ])).

    Definition square_loop: com :=
      WHILE BLe (ANum 1) (AId X) DO
        Y ::= AMult (AId Y) (AId Y);
        X ::= AMinus (AId X) (ANum 1)
      END.

    Example pe_loop_example1:
      square_loop / []
      || (WHILE BLe (ANum 1) (AId X) DO
             (Y ::= AMult (AId Y) (AId Y);
              X ::= AMinus (AId X) (ANum 1)); SKIP
           END) / [] / SKIP.
    Proof. erewrite f_equal2 with (f := fun c st => _ / _ || c / st / SKIP).
      step PE_WhileFixed. step PE_WhileFixedEnd. reflexivity.
      reflexivity. reflexivity. Qed.

    Example pe_loop_example2:
      (X ::= ANum 3; square_loop) / []
      || (SKIP;
           (Y ::= AMult (AId Y) (AId Y); SKIP);
           (Y ::= AMult (AId Y) (AId Y); SKIP);
           (Y ::= AMult (AId Y) (AId Y); SKIP);
           SKIP) / [(X,0)] / SKIP.
    Proof. erewrite f_equal2 with (f := fun c st => _ / _ || c / st / SKIP).
      eapply PE_Seq. eapply PE_AssStatic. reflexivity.
      step PE_WhileLoop.
      step PE_WhileLoop.
      step PE_WhileLoop.
      step PE_WhileEnd.
      inversion H. inversion H. inversion H.
      reflexivity. reflexivity. Qed.

    Example pe_loop_example3:
      (Z ::= ANum 3; subtract_slowly) / []
      || (SKIP;
           IFB BNot (BEq (AId X) (ANum 0)) THEN
             (SKIP; X ::= AMinus (AId X) (ANum 1));
             IFB BNot (BEq (AId X) (ANum 0)) THEN
               (SKIP; X ::= AMinus (AId X) (ANum 1));
               IFB BNot (BEq (AId X) (ANum 0)) THEN
                 (SKIP; X ::= AMinus (AId X) (ANum 1));
                 WHILE BNot (BEq (AId X) (ANum 0)) DO
                   (SKIP; X ::= AMinus (AId X) (ANum 1)); SKIP
                 END;
                 SKIP; Z ::= ANum 0
               ELSE SKIP; Z ::= ANum 1 FI; SKIP
             ELSE SKIP; Z ::= ANum 2 FI; SKIP
           ELSE SKIP; Z ::= ANum 3 FI) / [] / SKIP.
    Proof. erewrite f_equal2 with (f := fun c st => _ / _ || c / st / SKIP).
      eapply PE_Seq. eapply PE_AssStatic. reflexivity.
      step PE_While.
      step PE_While.
      step PE_While.
      step PE_WhileFixed.
      step PE_WhileFixedEnd.
      reflexivity. inversion H. inversion H. inversion H.
      reflexivity. reflexivity. Qed.

    Example pe_loop_example4:
      (X ::= ANum 0;
       WHILE BLe (AId X) (ANum 2) DO
         X ::= AMinus (ANum 1) (AId X)
       END) / [] || (SKIP; WHILE BTrue DO SKIP END) / [(X,0)] / SKIP.
    Proof. erewrite f_equal2 with (f := fun c st => _ / _ || c / st / SKIP).
      eapply PE_Seq. eapply PE_AssStatic. reflexivity.
      step PE_WhileFixedLoop.
      step PE_WhileLoop.
      step PE_WhileFixedEnd.
      inversion H. reflexivity. reflexivity. reflexivity. Qed.

正しさ
~~~~~~

この部分評価器は1より大きい(有限)整数 n
について、ループをn回展開することができます。このため、正しさを示すためには、動的評価の構造についての帰納法ではなく、動的評価がループの本体に入る回数についての帰納法が必要です。

::

    Reserved Notation "c1 '/' st '||' st' '#' n"
      (at level 40, st at level 39, st' at level 39).

    Inductive ceval_count : com -> state -> state -> nat -> Prop :=
      | E'Skip : forall st,
          SKIP / st || st # 0
      | E'Ass  : forall st a1 n l,
          aeval st a1 = n ->
          (l ::= a1) / st || (update st l n) # 0
      | E'Seq : forall c1 c2 st st' st'' n1 n2,
          c1 / st  || st'  # n1 ->
          c2 / st' || st'' # n2 ->
          (c1 ; c2) / st || st'' # (n1 + n2)
      | E'IfTrue : forall st st' b1 c1 c2 n,
          beval st b1 = true ->
          c1 / st || st' # n ->
          (IFB b1 THEN c1 ELSE c2 FI) / st || st' # n
      | E'IfFalse : forall st st' b1 c1 c2 n,
          beval st b1 = false ->
          c2 / st || st' # n ->
          (IFB b1 THEN c1 ELSE c2 FI) / st || st' # n
      | E'WhileEnd : forall b1 st c1,
          beval st b1 = false ->
          (WHILE b1 DO c1 END) / st || st # 0
      | E'WhileLoop : forall st st' st'' b1 c1 n1 n2,
          beval st b1 = true ->
          c1 / st || st' # n1 ->
          (WHILE b1 DO c1 END) / st' || st'' # n2 ->
          (WHILE b1 DO c1 END) / st || st'' # S (n1 + n2)

      where "c1 '/' st '||' st' # n" := (ceval_count c1 st st' n).

    Tactic Notation "ceval_count_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "E'Skip" | Case_aux c "E'Ass" | Case_aux c "E'Seq"
      | Case_aux c "E'IfTrue" | Case_aux c "E'IfFalse"
      | Case_aux c "E'WhileEnd" | Case_aux c "E'WhileLoop" ].

    Hint Constructors ceval_count.

    Theorem ceval_count_complete: forall c st st',
      c / st || st' -> exists n, c / st || st' # n.
    Proof. intros c st st' Heval.
      induction Heval;
        try inversion IHHeval1;
        try inversion IHHeval2;
        try inversion IHHeval;
        eauto. Qed.

    Theorem ceval_count_sound: forall c st st' n,
      c / st || st' # n -> c / st || st'.
    Proof. intros c st st' n Heval. induction Heval; eauto. Qed.

    Theorem pe_compare_nil_lookup: forall pe_st1 pe_st2,
      pe_compare pe_st1 pe_st2 = [] ->
      forall V, pe_lookup pe_st1 V = pe_lookup pe_st2 V.
    Proof. intros pe_st1 pe_st2 H V.
      apply (pe_compare_correct pe_st1 pe_st2 V).
      rewrite H. reflexivity. Qed.

    Theorem pe_compare_nil_override: forall pe_st1 pe_st2,
      pe_compare pe_st1 pe_st2 = [] ->
      forall st, pe_override st pe_st1 = pe_override st pe_st2.
    Proof. intros pe_st1 pe_st2 H st.
      apply functional_extensionality. intros V.
      rewrite !pe_override_correct.
      apply pe_compare_nil_lookup with (V:=V) in H.
      rewrite H. reflexivity. Qed.

    Reserved Notation "c' '/' pe_st' '/' c'' '/' st '||' st'' '#' n"
      (at level 40, pe_st' at level 39, c'' at level 39,
       st at level 39, st'' at level 39).

    Inductive pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)
                             (st:state) (st'':state) (n:nat) : Prop :=
      | pe_ceval_count_intro : forall st' n',
        c' / st || st' ->
        c'' / pe_override st' pe_st' || st'' # n' ->
        n' <= n ->
        c' / pe_st' / c'' / st || st'' # n
      where "c' '/' pe_st' '/' c'' '/' st '||' st'' '#' n" :=
            (pe_ceval_count c' pe_st' c'' st st'' n).

    Hint Constructors pe_ceval_count.

    Lemma pe_ceval_count_le: forall c' pe_st' c'' st st'' n n',
      n' <= n ->
      c' / pe_st' / c'' / st || st'' # n' ->
      c' / pe_st' / c'' / st || st'' # n.
    Proof. intros c' pe_st' c'' st st'' n n' Hle H. inversion H.
      econstructor; try eassumption. omega. Qed.

    Theorem pe_com_complete:
      forall c pe_st pe_st' c' c'', c / pe_st || c' / pe_st' / c'' ->
      forall st st'' n,
      (c / pe_override st pe_st || st'' # n) ->
      (c' / pe_st' / c'' / st || st'' # n).
    Proof. intros c pe_st pe_st' c' c'' Hpe.
      pe_com_cases (induction Hpe) Case; intros st st'' n Heval;
      try (inversion Heval; subst;
           try (rewrite -> pe_bexp_correct, -> H in *; solve by inversion);
           []);
      eauto.
      Case "PE_AssStatic". econstructor. econstructor.
        rewrite -> pe_aexp_correct. rewrite <- pe_override_update_add.
        rewrite -> H. apply E'Skip. auto.
      Case "PE_AssDynamic". econstructor. econstructor. reflexivity.
        rewrite -> pe_aexp_correct. rewrite <- pe_override_update_remove.
        apply E'Skip. auto.
      Case "PE_Seq".
        edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
        inversion Hskip. subst.
        edestruct IHHpe2. eassumption.
        econstructor; eauto. omega.
      Case "PE_If". inversion Heval; subst.
        SCase "E'IfTrue". edestruct IHHpe1. eassumption.
          econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
          eapply E_Seq. eassumption. apply eval_assign.
          rewrite <- assign_removes. eassumption. eassumption.
        SCase "E_IfFalse". edestruct IHHpe2. eassumption.
          econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
          eapply E_Seq. eassumption. apply eval_assign.
          rewrite -> pe_compare_override.
          rewrite <- assign_removes. eassumption. eassumption.
      Case "PE_WhileLoop".
        edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
        inversion Hskip. subst.
        edestruct IHHpe2. eassumption.
        econstructor; eauto. omega.
      Case "PE_While". inversion Heval; subst.
        SCase "E_WhileEnd". econstructor. apply E_IfFalse.
          rewrite <- pe_bexp_correct. assumption.
          apply eval_assign.
          rewrite <- assign_removes. inversion H2; subst; auto.
          auto.
        SCase "E_WhileLoop".
          edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
          inversion Hskip. subst.
          edestruct IHHpe2. eassumption.
          econstructor. apply E_IfTrue.
          rewrite <- pe_bexp_correct. assumption.
          repeat eapply E_Seq; eauto. apply eval_assign.
          rewrite -> pe_compare_override, <- assign_removes. eassumption.
          omega.
      Case "PE_WhileFixedLoop". apply ex_falso_quodlibet.
        generalize dependent (S (n1 + n2)). intros n.
        clear - Case H H0 IHHpe1 IHHpe2. generalize dependent st.
        induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
        SCase "E'WhileEnd". rewrite pe_bexp_correct, H in H7. inversion H7.
        SCase "E'WhileLoop".
          edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
          inversion Hskip. subst.
          edestruct IHHpe2. eassumption.
          rewrite <- (pe_compare_nil_override _ _ H0) in H7.
          apply H1 in H7; [| omega]. inversion H7.
      Case "PE_WhileFixed". generalize dependent st.
        induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
        SCase "E'WhileEnd". rewrite pe_bexp_correct in H8. eauto.
        SCase "E'WhileLoop". rewrite pe_bexp_correct in H5.
          edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
          inversion Hskip. subst.
          edestruct IHHpe2. eassumption.
          rewrite <- (pe_compare_nil_override _ _ H1) in H8.
          apply H2 in H8; [| omega]. inversion H8.
          econstructor; [ eapply E_WhileLoop; eauto | eassumption | omega].
    Qed.

    Theorem pe_com_sound:
      forall c pe_st pe_st' c' c'', c / pe_st || c' / pe_st' / c'' ->
      forall st st'' n,
      (c' / pe_st' / c'' / st || st'' # n) ->
      (c / pe_override st pe_st || st'').
    Proof. intros c pe_st pe_st' c' c'' Hpe.
      pe_com_cases (induction Hpe) Case;
        intros st st'' n [st' n' Heval Heval' Hle];
        try (inversion Heval; []; subst);
        try (inversion Heval'; []; subst); eauto.
      Case "PE_AssStatic". rewrite <- pe_override_update_add. apply E_Ass.
        rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
      Case "PE_AssDynamic". rewrite <- pe_override_update_remove. apply E_Ass.
        rewrite <- pe_aexp_correct. reflexivity.
      Case "PE_Seq". eapply E_Seq; eauto.
      Case "PE_IfTrue". apply E_IfTrue.
        rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
        eapply IHHpe. eauto.
      Case "PE_IfFalse". apply E_IfFalse.
        rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
        eapply IHHpe. eauto.
      Case "PE_If". inversion Heval; subst; inversion H7; subst; clear H7.
        SCase "E_IfTrue".
          eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
          rewrite <- assign_removes in Heval'.
          apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
          eapply IHHpe1. eauto.
        SCase "E_IfFalse".
          eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
          rewrite -> pe_compare_override in Heval'.
          rewrite <- assign_removes in Heval'.
          apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
          eapply IHHpe2. eauto.
      Case "PE_WhileEnd". apply E_WhileEnd.
        rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
      Case "PE_WhileLoop". eapply E_WhileLoop.
        rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
        eapply IHHpe1. eauto. eapply IHHpe2. eauto.
      Case "PE_While". inversion Heval; subst.
        SCase "E_IfTrue".
          inversion H9. subst. clear H9.
          inversion H10. subst. clear H10.
          eapply ceval_deterministic in H11; [| apply eval_assign]. subst.
          rewrite -> pe_compare_override in Heval'.
          rewrite <- assign_removes in Heval'.
          eapply E_WhileLoop. rewrite -> pe_bexp_correct. assumption.
          eapply IHHpe1. eauto.
          eapply IHHpe2. eauto.
        SCase "E_IfFalse". apply ceval_count_sound in Heval'.
          eapply ceval_deterministic in H9; [| apply eval_assign]. subst.
          rewrite <- assign_removes in Heval'.
          inversion H2; subst.
          SSCase "c2'' = SKIP". inversion Heval'. subst. apply E_WhileEnd.
            rewrite -> pe_bexp_correct. assumption.
          SSCase "c2'' = WHILE b1 DO c1 END". assumption.
      Case "PE_WhileFixedEnd". eapply ceval_count_sound. apply Heval'.
      Case "PE_WhileFixedLoop".
        apply loop_never_stops in Heval. inversion Heval.
      Case "PE_WhileFixed".
        clear - Case H1 IHHpe1 IHHpe2 Heval.
        remember (WHILE pe_bexp pe_st b1 DO c1'; c2' END) as c'.
        ceval_cases (induction Heval) SCase;
          inversion Heqc'; subst; clear Heqc'.
        SCase "E_WhileEnd". apply E_WhileEnd.
          rewrite pe_bexp_correct. assumption.
        SCase "E_WhileLoop".
          assert (IHHeval2' := IHHeval2 (refl_equal _)).
          apply ceval_count_complete in IHHeval2'. inversion IHHeval2'.
          clear IHHeval1 IHHeval2 IHHeval2'.
          inversion Heval1. subst.
          eapply E_WhileLoop. rewrite pe_bexp_correct. assumption. eauto.
          eapply IHHpe2. econstructor. eassumption.
          rewrite <- (pe_compare_nil_override _ _ H1). eassumption. apply le_n.
    Qed.

    Corollary pe_com_correct:
      forall c pe_st pe_st' c', c / pe_st || c' / pe_st' / SKIP ->
      forall st st'',
      (c / pe_override st pe_st || st'') <->
      (exists st', c' / st || st' /\ pe_override st' pe_st' = st'').
    Proof. intros c pe_st pe_st' c' H st st''. split.
      Case "->". intros Heval.
        apply ceval_count_complete in Heval. inversion Heval as [n Heval'].
        apply pe_com_complete with (st:=st) (st'':=st'') (n:=n) in H.
        inversion H as [? ? ? Hskip ?]. inversion Hskip. subst. eauto.
        assumption.
      Case "<-". intros [st' [Heval Heq]]. subst st''.
        eapply pe_com_sound in H. apply H.
        econstructor. apply Heval. apply E'Skip. apply le_n.
    Qed.

    End Loop.

フローチャートプログラムの部分評価
----------------------------------

命令型プログラムを部分評価する標準的アプローチは、\ ``WHILE``\ ループを直接部分評価する代わりに、それをフローチャート(*flowcharts*)に変換することです。言い換えると、言語にラベルとジャンプを追加すると、部分評価がずいぶん簡単になることがわかります。フローチャートを部分評価した結果は、残留フローチャートになります。ラッキーな場合は、残留フローチャートのジャンプは\ ``WHILE``\ ループに戻すことができます。ただし、これは一般にできるわけではありません。ここではこのことは追求しません。

基本ブロック
~~~~~~~~~~~~

フローチャートは基本ブロック(*basic
blocks*)から成ります。これをここでは、帰納型\ ``block``\ で表します。基本ブロックは、代入(コンストラクタ\ ``Assign``)の列の最後に条件ジャンプ(コンストラクタ\ ``If``)または無条件ジャンプ(コンストラクタ\ ``Goto``)が付いたものです。ジャンプ先は任意の型のラベル(*labels*)で特定されます。これから、\ ``block``\ 型をラベルの型でパラメータ化します。

::

    Inductive block (Label:Type) : Type :=
      | Goto : Label -> block Label
      | If : bexp -> Label -> Label -> block Label
      | Assign : id -> aexp -> block Label -> block Label.

    Tactic Notation "block_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "Goto" | Case_aux c "If" | Case_aux c "Assign" ].

    Implicit Arguments Goto   [[Label]].
    Implicit Arguments If     [[Label]].
    Implicit Arguments Assign [[Label]].

以下では、上述のImpによる「奇数/偶数」プログラムを、全体を通した例として使います。このプログラムをフローチャートに変換するには、4つのラベルが必要です。それを以下のように定義します。

::

    Inductive parity_label : Type :=
      | entry : parity_label
      | loop  : parity_label
      | body  : parity_label
      | done  : parity_label.

以下の\ ``block``\ は例プログラムの\ ``body``\ ラベルに対する基本ブロックです。

::

    Definition parity_body : block parity_label :=
      Assign Y (AMinus (AId Y) (ANum 1))
       (Assign X (AMinus (ANum 1) (AId X))
         (Goto loop)).

与えられた初期状態で基本ブロックを評価することは、最終状態と次にジャンプするためのラベルを計算することです。基本ブロックはループや他の制御構造を含まないことから、基本ブロックの評価は全関数です。非停止性の心配をする必要はありません。

::

    Fixpoint keval {L:Type} (st:state) (k : block L) : state * L :=
      match k with
      | Goto l => (st, l)
      | If b l1 l2 => (st, if beval st b then l1 else l2)
      | Assign i a k => keval (update st i (aeval st a)) k
      end.

    Example keval_example:
      keval empty_state parity_body
      = (update (update empty_state Y 0) X 1, loop).
    Proof. reflexivity. Qed.

フローチャートプログラム
~~~~~~~~~~~~~~~~~~~~~~~~

フローチャートプログラムは単にラベルを基本ブロックに写像する検索関数です。実際には、いくつかのラベルは停止状態(*halting
states*)で、基本ブロックには写像されません。これから、より正確には、ラベルの型が\ ``L``\ であるフローチャート\ ``program``\ は\ ``L``\ から\ ``option (block L)``\ への関数です。

::

    Definition program (L:Type) : Type := L -> option (block L).

    Definition parity : program parity_label := fun l =>
      match l with
      | entry => Some (Assign X (ANum 0) (Goto loop))
      | loop => Some (If (BLe (ANum 1) (AId Y)) body done)
      | body => Some parity_body
      | done => None

基本ブロックとは異なり、プログラムは停止しないこともあります。これからプログラムの評価は再帰関数ではなく帰納的関係\ ``peval``\ でモデル化します。

::

    Inductive peval {L:Type} (p : program L)
      : state -> L -> state -> L -> Prop :=
      | E_None: forall st l,
        p l = None ->
        peval p st l st l
      | E_Some: forall st l k st' l' st'' l'',
        p l = Some k ->
        keval st k = (st', l') ->
        peval p st' l' st'' l'' ->
        peval p st l st'' l''.

    Example parity_eval: peval parity empty_state entry empty_state done.
    Proof. erewrite f_equal with (f := fun st => peval _ _ _ st _).
      eapply E_Some. reflexivity. reflexivity.
      eapply E_Some. reflexivity. reflexivity.
      apply E_None. reflexivity.
      apply functional_extensionality. intros i. rewrite update_same; auto.
    Qed.

    Tactic Notation "peval_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "E_None" | Case_aux c "E_Some" ].

基本ブロックとフローチャートプログラムの部分評価
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

部分評価はラベルの型を体系的に変更します。もとのラベルの型が\ ``L``\ ならば、\ ``pe_state * L``\ になります。そして、オリジナルプログラムと同じラベルが、異なる部分状態と対にされることで、複数のラベルに拡大されます。例えば、\ ``parity``\ プログラムのラベル\ ``loop``\ は2つのラベル:``([(X,0)``,
loop)] と\ ``([(X,1)``, loop)]
になります。このラベルの型の変更は以前に定義した\ ``pe_block``\ と\ ``pe_program``\ の型に反映されます。

::

    Fixpoint pe_block {L:Type} (pe_st:pe_state) (k : block L)
      : block (pe_state * L) :=
      match k with
      | Goto l => Goto (pe_st, l)
      | If b l1 l2 =>
        match pe_bexp pe_st b with
        | BTrue  => Goto (pe_st, l1)
        | BFalse => Goto (pe_st, l2)
        | b'     => If b' (pe_st, l1) (pe_st, l2)
        end
      | Assign i a k =>
        match pe_aexp pe_st a with
        | ANum n => pe_block (pe_add pe_st i n) k
        | a' => Assign i a' (pe_block (pe_remove pe_st i) k)
        end
      end.

    Example pe_block_example:
      pe_block [(X,0)] parity_body
      = Assign Y (AMinus (AId Y) (ANum 1)) (Goto ([(X,1)], loop)).
    Proof. reflexivity. Qed.

    Theorem pe_block_correct: forall (L:Type) st pe_st k st' pe_st' (l':L),
      keval st (pe_block pe_st k) = (st', (pe_st', l')) ->
      keval (pe_override st pe_st) k = (pe_override st' pe_st', l').
    Proof. intros. generalize dependent pe_st. generalize dependent st.
      block_cases (induction k as [l | b l1 l2 | i a k]) Case;
        intros st pe_st H.
      Case "Goto". inversion H; reflexivity.
      Case "If".
        replace (keval st (pe_block pe_st (If b l1 l2)))
           with (keval st (If (pe_bexp pe_st b) (pe_st, l1) (pe_st, l2)))
           in H by (simpl; destruct (pe_bexp pe_st b); reflexivity).
        simpl in *. rewrite pe_bexp_correct.
        destruct (beval st (pe_bexp pe_st b)); inversion H; reflexivity.
      Case "Assign".
        simpl in *. rewrite pe_aexp_correct.
        destruct (pe_aexp pe_st a); simpl;
          try solve [rewrite pe_override_update_add; apply IHk; apply H];
          solve [rewrite pe_override_update_remove; apply IHk; apply H].
    Qed.

    Definition pe_program {L:Type} (p : program L)
      : program (pe_state * L) :=
      fun pe_l => match pe_l with (pe_st, l) =>
                    option_map (pe_block pe_st) (p l)
                  end.

    Inductive pe_peval {L:Type} (p : program L)
      (st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : Prop :=
      | pe_peval_intro : forall st' pe_st',
        peval (pe_program p) st (pe_st, l) st' (pe_st', l') ->
        pe_override st' pe_st' = st'o ->
        pe_peval p st pe_st l st'o l'.

    Theorem pe_program_correct:
      forall (L:Type) (p : program L) st pe_st l st'o l',
      peval p (pe_override st pe_st) l st'o l' <->
      pe_peval p st pe_st l st'o l'.
    Proof. intros.
      split; [Case "->" | Case "<-"].
      Case "->". intros Heval.
        remember (pe_override st pe_st) as sto.
        generalize dependent pe_st. generalize dependent st.
        peval_cases (induction Heval as
          [ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ])
          SCase; intros st pe_st Heqsto; subst sto.
        SCase "E_None". eapply pe_peval_intro. apply E_None.
          simpl. rewrite Hlookup. reflexivity. reflexivity.
        SCase "E_Some".
          remember (keval st (pe_block pe_st k)) as x.
          destruct x as [st' [pe_st' l'_]].
          symmetry in Heqx. erewrite pe_block_correct in Hkeval by apply Heqx.
          inversion Hkeval. subst st'o l'_. clear Hkeval.
          edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.
          eapply pe_peval_intro; [| reflexivity]. eapply E_Some; eauto.
          simpl. rewrite Hlookup. reflexivity.
      Case "<-". intros [st' pe_st' Heval Heqst'o].
        remember (pe_st, l) as pe_st_l.
        remember (pe_st', l') as pe_st'_l'.
        generalize dependent pe_st. generalize dependent l.
        peval_cases (induction Heval as
          [ st [pe_st_ l_] Hlookup
          | st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']
            Hlookup Hkeval Heval ])
          SCase; intros l pe_st Heqpe_st_l;
          inversion Heqpe_st_l; inversion Heqpe_st'_l'; repeat subst.
        SCase "E_None". apply E_None. simpl in Hlookup.
          destruct (p l'); [ solve [ inversion Hlookup ] | reflexivity ].
        SCase "E_Some".
          simpl in Hlookup. remember (p l) as k.
          destruct k as [k|]; inversion Hlookup; subst.
          eapply E_Some; eauto. apply pe_block_correct. apply Hkeval.
    Qed.

