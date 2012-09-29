Lists\_J: 直積、リスト、オプション
==================================

次の行を実行すると、前章の定義を一度にインポートすることができます。

::

    Require Export Basics_J.

ただしこれを使うには、\ ``coqc``\ を使って\ ``Basics_J.v``\ をコンパイルし、\ ``Basics_J.vo``\ を作成しておく必要があります。（これは、
.java ファイルから .class ファイルを作ったり、 .c ファイルから .o
ファイルを作ったりするのと同じことです。）

コードをコンパイルする方法はふたつあります。

-  CoqIDE:Basics\_J.v を開き、 "Compile" メニューの "Compile Buffer"
   をクリックする。
-  コマンドライン:``coqc Basics_J.v``\ を実行する。

このファイルでも\ ``Module``\ 機能を使って数のリストやペアの定義を囲んでおきます。こうしておくことで、同じ操作を改良した（一般化した）ものに同じ名前をつけることができます。

::

    Module NatList.

数のペア
--------

``Inductive``\ による型定義では、各構成子は任意の個数の引数を取ることができました。\ ``true``\ や\ ``O``\ のように引数のないもの、\ ``S``\ のようにひとつのもの、また、ふたつ以上の取るものも以下のように定義することができます。

::

    Inductive natprod : Type :=
      pair : nat -> nat -> natprod.

この定義は以下のように読めます。すなわち、「数のペアを構成する方法がただひとつある。それは、構成子\ ``pair``\ を\ ``nat``\ 型のふたつの引数に適用することである」。

次に示すのは二引数の構成子に対してパターンマッチをする簡単な関数の定義です。

::

    Definition fst (p : natprod) : nat :=
      match p with
      | pair x y => x
      end.
    Definition snd (p : natprod) : nat :=
      match p with
      | pair x y => y
      end.

ペアはよく使うものなので、\ ``pair x y``\ ではなく、数学の標準的な記法で\ ``(x, y)``\ と書けるとよいでしょう。このような記法を使うためには\ ``Notation``\ 宣言を使います。

::

    Notation "( x , y )" := (pair x y).

こうして定義した新しい記法（notation）は、式だけでなくパターンマッチに使うこともできます。（実際には、前章でも見たように、この記法は標準ライブラリの一部として提供されています。）

::

    Eval simpl in (fst (3,4)).

    Definition fst' (p : natprod) : nat :=
      match p with
      | (x,y) => x
      end.
    Definition snd' (p : natprod) : nat :=
      match p with
      | (x,y) => y
      end.

    Definition swap_pair (p : natprod) : natprod :=
      match p with
      | (x,y) => (y,x)
      end.

それでは、数のペアに関する簡単な事実をいくつか証明してみましょう。補題を一定の（一種独特な）形式で書いておけば、単に
reflexivity（と組み込みの簡約）だけで証明することができます。

::

    Theorem surjective_pairing' : forall (n m : nat),
      (n,m) = (fst (n,m), snd (n,m)).
    Proof.
      reflexivity.  Qed.

しかし、補題を以下のようにより自然な書き方をした場合は、反射律では足りません。

::

    Theorem surjective_pairing_stuck : forall (p : natprod),
      p = (fst p, snd p).
    Proof.
      simpl. 
    Admitted.

``simpl``\ で\ ``fst``\ や\ ``snd``\ の中のパターンマッチを実行できるよう、\ ``p``\ の構造を明らかにする必要があります。これには\ ``destruct``\ を使います。

``nat``\ の場合と異なり、\ ``destruct``\ でサブゴールが増えることはありません。これは、\ ``natprod``\ の構成法がひとつしかないからです。

::

    Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
    Proof.
      intros p.  destruct p as (n,m).  simpl.  reflexivity.  Qed.

先ほど宣言した記法を "``as``..."
パターンで束縛する変数を指定するために使っています。

練習問題: ★ (snd\_fst\_is\_swap)
''''''''''''''''''''''''''''''''

::

    Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

数のリスト
----------

ペアの定義を少し一般化すると、数のリストは次のように表すことができます。すなわち、「リストは、空のリストであるか、または数と他のリストをペアにしたものである」。

::

    Inductive natlist : Type :=
      | nil : natlist
      | cons : nat -> natlist -> natlist.

たとえば、次の定義は要素が三つのリストです

::

    Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

ペアの場合と同じく、リストをプログラミング言語で馴染んだ記法で書くことができると便利でしょう。次のふたつの宣言では\ ``::``\ を中置の\ ``cons``\ 演算子として使えるようにし、角括弧をリストを構成するための外置（outfix）記法として使えるようにしています。

::

    Notation "x :: l" := (cons x l) (at level 60, right associativity).
    Notation "[ ]" := nil.
    Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

この宣言を完全に理解する必要はありませんが、興味のある読者のために簡単に説明しておきます。

``right associativity``\ アノテーションは複数の\ ``::``\ を使った式にどのように括弧を付けるか指示するものです。例えば、次のみっつの宣言はすべて同じ意味に解釈されます。

::

    Definition l_123'   := 1 :: (2 :: (3 :: nil)).
    Definition l_123''  := 1 :: 2 :: 3 :: nil.
    Definition l_123''' := [1,2,3].

``at level 60``\ の部分は\ ``::``\ を他の中置演算子といっしょに使っている式にどのように括弧を付けるかを指示するものです。例えば、\ ``+``\ を\ ``plus``\ に対する
level 50 の中置記法として定義したので、

::

    Notation "x + y" := (plus x y)
                        (at level 50, left associativity).

``+``\ は\ ``::``\ よりも強く結合し、\ ``1 + 2 :: [3``]
は期待通り、\ ``1 + (2 :: [3``)] ではなく\ ``(1 + 2) :: [3``]
と構文解析されます。

（ところで、 .v ファイルを読んでいるときには "``1 + 2 :: [3``]"
のような書き方は少し読みにくいように感じるでしょう。内側の 3
の左右の角括弧はリストを表すものですが、外側の括弧は coqdoc
用の命令で、角括弧内の部分をそのままのテキストではなく Coq
のコードとして表示するよう指示するものです。この角括弧は生成された HTML
には現れません。）

上の二番目と三番目の\ ``Notation``\ 宣言は標準的なリストの記法を導入するためのものです。三番目の\ ``Notation``\ の右辺は、
n 引数の記法を二項構成子の入れ子に変換する記法を定義するための Coq
の構文の例です。

リストを操作するために便利な関数がいくつかあります。例えば、\ ``repeat``\ 関数は数\ ``n``\ と\ ``count``\ を取り、各要素が\ ``n``\ で長さ\ ``count``\ のリストを返します。

::

    Fixpoint repeat (n count : nat) : natlist :=
      match count with
      | O => nil
      | S count' => n :: (repeat n count')
      end.

``length``\ 関数はリストの長さを計算します。

::

    Fixpoint length (l:natlist) : nat :=
      match l with
      | nil => O
      | h :: t => S (length t)
      end.

``app``\ （"append"）関数はふたつのリストを連結します。

::

    Fixpoint app (l1 l2 : natlist) : natlist :=
      match l1 with
      | nil    => l2
      | h :: t => h :: (app t l2)
      end.

``app``\ はこの後でよく使うので、中置演算子を用意しておくと便利でしょう。

::

    Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).

    Example test_app1:             [1,2,3] ++ [4,5] = [1,2,3,4,5].
    Proof. reflexivity.  Qed.
    Example test_app2:             nil ++ [4,5] = [4,5].
    Proof. reflexivity.  Qed.
    Example test_app3:             [1,2,3] ++ nil = [1,2,3].
    Proof. reflexivity.  Qed.

もうふたつリストを使った例を見てみましょう。\ ``hd``\ 関数はリストの最初の要素（先頭——
head）を返し、\ ``tail``\ は最初の要素を除いたものを返します。空のリストには最初の要素はありませんから、その場合に返す値を引数として渡しておかなければなりません。

::

    Definition hd (default:nat) (l:natlist) : nat :=
      match l with
      | nil => default
      | h :: t => h
      end.

    Definition tail (l:natlist) : natlist :=
      match l with
      | nil => nil
      | h :: t => t
      end.

    Example test_hd1:             hd 0 [1,2,3] = 1.
    Proof. reflexivity.  Qed.
    Example test_hd2:             hd 0 [] = 0.
    Proof. reflexivity.  Qed.
    Example test_tail:            tail [1,2,3] = [2,3].
    Proof. reflexivity.  Qed.

練習問題: ★★, recommended (list\_funs)
''''''''''''''''''''''''''''''''''''''

以下の\ ``nonzeros``\ 、\ ``oddmembers``\ 、\ ``countoddmembers``\ の定義を完成させなさい。

::

    Fixpoint nonzeros (l:natlist) : natlist :=
      (* FILL IN HERE *) admit.

    Example test_nonzeros:            nonzeros [0,1,0,2,3,0,0] = [1,2,3].
     (* FILL IN HERE *) Admitted.

    Fixpoint oddmembers (l:natlist) : natlist :=
      (* FILL IN HERE *) admit.

    Example test_oddmembers:            oddmembers [0,1,0,2,3,0,0] = [1,3].
     (* FILL IN HERE *) Admitted.

    Fixpoint countoddmembers (l:natlist) : nat :=
      (* FILL IN HERE *) admit.

    Example test_countoddmembers1:    countoddmembers [1,0,3,1,4,5] = 4.
     (* FILL IN HERE *) Admitted.
    Example test_countoddmembers2:    countoddmembers [0,2,4] = 0.
     (* FILL IN HERE *) Admitted.
    Example test_countoddmembers3:    countoddmembers nil = 0.
     (* FILL IN HERE *) Admitted.

☐

練習問題: ★★ (alternate)
''''''''''''''''''''''''

``alternate``\ の定義を完成させなさい。この関数は、ふたつのリストから交互に要素を取り出しひとつに「綴じ合わせる」関数です。具体的な例は下のテストを見てください。

注意:``alternate``\ の自然な定義のひとつは、
「\ ``Fixpoint``\ による定義は『明らかに停止する』ものでなければならない」という
Coq
の要求を満たすことができません。このパターンにはまってしまったようであれば、両方のリストの要素を同時に見ていくような少し冗長な方法を探してみてください。

::

    Fixpoint alternate (l1 l2 : natlist) : natlist :=
      (* FILL IN HERE *) admit.

    Example test_alternate1:        alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
     (* FILL IN HERE *) Admitted.
    Example test_alternate2:        alternate [1] [4,5,6] = [1,4,5,6].
     (* FILL IN HERE *) Admitted.
    Example test_alternate3:        alternate [1,2,3] [4] = [1,4,2,3].
     (* FILL IN HERE *) Admitted.
    Example test_alternate4:        alternate [] [20,30] = [20,30].
     (* FILL IN HERE *) Admitted.

☐

リストを使ったバッグ
~~~~~~~~~~~~~~~~~~~~

バッグ（\ ``bag``\ 。または多重集合——``multiset``\ ）は集合のようなものですが、それぞれの要素が一度ではなく複数回現れることのできるようなものを言います。バッグの実装としてありうるのは数のバッグをリストで表現するというものでしょう。

::

    Definition bag := natlist.

練習問題: ★★★ (bag\_functions)
''''''''''''''''''''''''''''''

バッグに対する\ ``count``\ 、\ ``sum``\ 、\ ``add``\ 、\ ``member``\ 関数の定義を完成させなさい。

::

    Fixpoint count (v:nat) (s:bag) : nat :=
      (* FILL IN HERE *) admit.

下の証明はすべて\ ``reflexivity``\ だけでできます。

::

    Example test_count1:              count 1 [1,2,3,1,4,1] = 3.
     (* FILL IN HERE *) Admitted.
    Example test_count2:              count 6 [1,2,3,1,4,1] = 0.
     (* FILL IN HERE *) Admitted.

多重集合の\ ``sum``\ （直和。または非交和）は集合の\ ``union``\ （和）と同じようなものです。\ ``sum a b``\ は\ ``a``\ と\ ``b``\ の両方の要素を持つ多重集合です。（数学者は通常、多重集合の\ ``union``\ にもう少し異なる定義を与えます。それが、この関数の名前を\ ``union``\ にしなかった理由です。）\ ``sum``\ のヘッダには引数の名前を与えませんでした。さらに、\ ``Fixpoint``\ ではなく\ ``Definition``\ を使っています。ですから、引数に名前がついていたとしても再帰的な処理はできません。問題をこのように設定したのは、\ ``sum``\ を（定義済みの関数を使うといった）別の方法で定義できないか考えさせるためです。

::

    Definition sum : bag -> bag -> bag :=
      (* FILL IN HERE *) admit.

    Example test_sum1:              count 1 (sum [1,2,3] [1,4,1]) = 3.
     (* FILL IN HERE *) Admitted.

    Definition add (v:nat) (s:bag) : bag :=
      (* FILL IN HERE *) admit.

    Example test_add1:                count 1 (add 1 [1,4,1]) = 3.
     (* FILL IN HERE *) Admitted.
    Example test_add2:                count 5 (add 1 [1,4,1]) = 0.
     (* FILL IN HERE *) Admitted.

    Definition member (v:nat) (s:bag) : bool :=
      (* FILL IN HERE *) admit.

    Example test_member1:             member 1 [1,4,1] = true.
     (* FILL IN HERE *) Admitted.
    Example test_member2:             member 2 [1,4,1] = false.
     (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★, optional (bag\_more\_functions)
''''''''''''''''''''''''''''''''''''''''''''''

練習として、さらにいくつかの関数を作成してください。

::

    Fixpoint remove_one (v:nat) (s:bag) : bag :=


      (* FILL IN HERE *) admit.

    Example test_remove_one1:         count 5 (remove_one 5 [2,1,5,4,1]) = 0.
     (* FILL IN HERE *) Admitted.
    Example test_remove_one2:         count 5 (remove_one 5 [2,1,4,1]) = 0.
     (* FILL IN HERE *) Admitted.
    Example test_remove_one3:         count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
     (* FILL IN HERE *) Admitted.
    Example test_remove_one4:
      count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
     (* FILL IN HERE *) Admitted.

    Fixpoint remove_all (v:nat) (s:bag) : bag :=
      (* FILL IN HERE *) admit.

    Example test_remove_all1:          count 5 (remove_all 5 [2,1,5,4,1]) = 0.
     (* FILL IN HERE *) Admitted.
    Example test_remove_all2:          count 5 (remove_all 5 [2,1,4,1]) = 0.
     (* FILL IN HERE *) Admitted.
    Example test_remove_all3:          count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
     (* FILL IN HERE *) Admitted.
    Example test_remove_all4:          count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
     (* FILL IN HERE *) Admitted.

    Fixpoint subset (s1:bag) (s2:bag) : bool :=
      (* FILL IN HERE *) admit.

    Example test_subset1:              subset [1,2] [2,1,4,1] = true.
     (* FILL IN HERE *) Admitted.
    Example test_subset2:              subset [1,2,2] [2,1,4,1] = false.
     (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★, recommended (bag\_theorem)
'''''''''''''''''''''''''''''''''''''''''

::

    []
     *)

FILL IN HERE
``count``\ や\ ``add``\ を使ったバッグに関する面白い定理書き、それを証明しなさい。この問題はいわゆる自由課題で、真になることがわかっていても、証明にはまだ習っていない技を使わなければならない定理を思いついてしまうこともあります。証明に行き詰まってしまったら気軽に質問してください。

(\* FILL IN HERE \*)☐

リストに関する推論
------------------

数の場合と同じく、リスト処理関数についての簡単な事実はもっぱら簡約のみで証明できることがあります。たとえば、次の定理は\ ``reflexivity``\ で行われる簡約だけで証明できます。

::

    Theorem nil_app : forall l:natlist,
      [] ++ l = l.
    Proof.
       reflexivity.  Qed.

これは、\ ``[``]
が\ ``app``\ の定義のパターンマッチ部分に代入され、パターンマッチ自体が簡約できるようになるからです。

またこれも数の場合と同じように、未知のリストの形（空であるかどうか）に応じた場合分けも有効です。

::

    Theorem tl_length_pred : forall l:natlist,
      pred (length l) = length (tail l).
    Proof.
      intros l. destruct l as [| n l'].
      Case "l = nil".
        reflexivity.
      Case "l = cons n l'".
        reflexivity.  Qed.

ここで、\ ``nil``\ の場合がうまく行くのは、\ ``tl nil = nil``\ と定義したからです。ここでは、\ ``destruct``\ タクティックの\ ``as``\ で\ ``n``\ と\ ``l'``\ のふたつの名前を導入しました。これは、リストの\ ``cons``\ 構成子が引数をふたつ（構成するリストの頭部と尾部）取ることに対応しています。

ただし、リストに関する興味深い定理の証明には、帰納法が必要になるのが普通です。

お小言
~~~~~~

単に例題の証明を読んでいるだけでは大きな進歩は望めません！ 各証明を実際に
Coq
で動かし、各ステップがその証明にどのようにかかわっているか考え、道筋をていねいになぞっていくことがとても大切です。そうしなければ、演習には何の意味もありません。

リスト上の帰納法
~~~~~~~~~~~~~~~~

``natlist``\ のようなデータ型に対して帰納法で証明をするのは、普通の自然数に対する帰納法よりも馴染みにくさを感じたことでしょう。しかし、基本的な考え方は同じくらい簡単です。\ ``Inductive``\ 宣言では、宣言した構成子から構築できるデータ方の集合を定義しています。例えば、ブール値では\ ``true``\ と\ ``false``\ のいずれかであり、数では\ ``O``\ か数に対する\ ``S``\ のいずれか、リストであれば\ ``nil``\ か数とリストに対する\ ``cons``\ のいずれかです。

さらに言えば、帰納的に定義された集合の要素になるのは、宣言した構成子を互いに適用したものだけです。このことがそのまま帰納的に定義された集合に関する推論の方法になります。すなわち、数は\ ``O``\ であるか、より小さい数に\ ``S``\ を適用したものであるかのいずれかです。リストは\ ``nil``\ であるか、何らかの数とより小さいリストに\ ``cons``\ を適用したものです。他のものも同様です。ですから、あるリスト\ ``l``\ に関する命題\ ``P``\ があり、\ ``P``\ がすべてのリストに対して成り立つことを示したい場合には、次のように推論します。

-  まず、\ ``l``\ が\ ``nil``\ のとき\ ``P``\ が\ ``l``\ について成り立つことを示す。
-  それから、\ ``l``\ が\ ``cons n l'``\ であるとき、ある数\ ``n``\ とより小さいリスト\ ``l'``\ に対して、\ ``P``\ が\ ``l'``\ について成り立つと仮定すれば\ ``P``\ が\ ``l``\ についても成り立つことを示す。

大きなリストはそれより小さなリストから作り出され、少しずつ\ ``nil``\ に近付いて行きます。よって、このふたつのことからすべてのリスト\ ``l``\ に関して\ ``P``\ が真であることが言えます。具体的な例で説明しましょう。

::

    Theorem app_ass : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
    Proof.
      intros l1 l2 l3. induction l1 as [| n l1'].
      Case "l1 = nil".
        reflexivity.
      Case "l1 = cons n l1'".
        simpl. rewrite -> IHl1'. reflexivity.  Qed.

蒸し返すようですが、この Coq
の証明はこうして単に静的なテキストとして読んでいる限り、さほど明白で分かりやすいものではありません。
Coq の証明は、 Coq
を対話的に動かしながらポイントごとに「現在のゴールは何か」「コンテキストに何が出ているか」を見て、証明が今どうなっているかを読み下していくことで理解されるようになっています。しかし、このような証明の途中経過は、全てが証明結果として書き出されるわけではありません。だからこそ、人間向けの自然言語での証明には証明の筋道がわかるように証明の指針を書いておく必要があるのです。特に、読者が流れを見失わないよう、ふたつめの場合分けで使う帰納法の仮定が何だったのかわかるようにしておくのは有益なはずです。

定理:
任意のリスト\ ``l1``\ 、\ ``l2``\ 、\ ``l3``\ について、\ ``(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)``\ が成り立つ。

証明:``l1``\ についての帰納法で証明する

-  まず、\ ``l1 = [``] と仮定して

   ::

          ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3)

を示す。これは\ ``++``\ の定義から自明である。

-  次に\ ``l1 = n::l1'``\ かつ

   ::

          (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

（帰納法の仮定）と仮定して

::

           ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3)

を示す。\ ``++``\ の定義から、この式は以下のように変形できる。

::

           n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3))

これは帰納法の仮定から直接導かれる。☐

下の練習問題は授業中に解きましょう。

::

    Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
    Proof.

      intros l1 l2. induction l1 as [| n l1'].
      Case "l1 = nil".
        reflexivity.
      Case "l1 = cons".
        simpl. rewrite -> IHl1'. reflexivity.  Qed.

リストに対する帰納的証明のもう少し入り組んだ例を見てみましょう。リストの右側に\ ``cons``\ する関数\ ``snoc``\ を定義したとしましょう。

::

    Fixpoint snoc (l:natlist) (v:nat) : natlist :=
      match l with
      | nil    => [v]
      | h :: t => h :: (snoc t v)
      end.

この関数を使ってリストの反転関数\ ``rev``\ を定義します。

::

    Fixpoint rev (l:natlist) : natlist :=
      match l with
      | nil    => nil
      | h :: t => snoc (rev t) h
      end.

    Example test_rev1:            rev [1,2,3] = [3,2,1].
    Proof. reflexivity.  Qed.
    Example test_rev2:            rev nil = nil.
    Proof. reflexivity.  Qed.

新しく定義した\ ``snoc``\ と\ ``rev``\ に関する定理を証明してみましょう。ここまでの帰納的証明よりも難易度の高いものですが、リストを反転しても長さの変わらないことを証明します。下の方法では、ふたつめの場合分けで行き詰まってしまいます。

::

    Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
    Proof.
      intros l. induction l as [| n l'].
      Case "l = []".
        reflexivity.
      Case "l = n :: l'".
        simpl. 

    Admitted.

この\ ``snoc``\ に関する等式が成り立つことを示せれば証明が先に進むはずです。この式を取り出して別個の補題として証明してみましょう。

::

    Theorem length_snoc : forall n : nat, forall l : natlist,
      length (snoc l n) = S (length l).
    Proof.
      intros n l. induction l as [| n' l'].
      Case "l = nil".
        reflexivity.
      Case "l = cons n' l'".
        simpl. rewrite -> IHl'. reflexivity.  Qed.

これで、元々の証明ができるようになりました。

::

    Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
    Proof.
      intros l. induction l as [| n l'].
      Case "l = nil".
        reflexivity.
      Case "l = cons".
        simpl. rewrite -> length_snoc.
        rewrite -> IHl'. reflexivity.  Qed.

対比として、この二つの定理の非形式的な証明を見てみましょう

定理:
任意の数\ ``n``\ とリスト\ ``l``\ について\ ``length (snoc l n) = S (length l)``\ が成り立つ。

証明:``l``\ についての帰納法で証明する。

-  まず、\ ``l = [``] と仮定して

   ::

           length (snoc [] n) = S (length [])

を示す。これは\ ``length``\ と\ ``snoc``\ の定義から直接導かれる。

-  次に、\ ``l = n'::l'``\ かつ

   ::

           length (snoc l' n) = S (length l')

と仮定して、

::

            length (snoc (n' :: l') n) = S (length (n' :: l'))

を示す。\ ``length``\ と\ ``snoc``\ の定義から次のように変形できる。

::

            S (length (snoc l' n)) = S (S (length l'))

これは帰納法の仮定から明らかである。☐

定理:
任意のリスト\ ``l``\ について\ ``length (rev l) = length l``\ が成り立つ。

証明:``l``\ についての帰納法で証明する。

-  まず、\ ``l = [``] と仮定して

   ::

             length (rev []) = length []

を示す。これは\ ``length``\ と\ ``rev``\ の定義から直接導かれる

-  次に、\ ``l = n::l'``\ かつ

   ::

             length (rev l') = length l'

と仮定して、

::

              length (rev (n :: l')) = length (n :: l')

を示す。\ ``rev``\ の定義から次のように変形できる。

::

              length (snoc (rev l') n) = S (length l')

これは、先程の補題から、次のものと同じである。

::

              S (length (rev l')) = S (length l')

これは、帰納法の仮定から明らかである。☐

こういった証明のスタイルは、どう見ても長ったらしく杓子定規な感じがします。最初の何回かは別にして、それ以後は、細かいところは省略してしまって（必要であれば、頭の中や紙の上で追うのは簡単です）、自明でないところにだけ注目した方がわかりやすいでしょう。そのように省略がちに書けば、上の証明は次のようになります。

定理:任意のリスト\ ``l``\ について\ ``length (rev l) = length l``\ が成り立つ。

証明: まず、任意の\ ``l``\ について

::

           length (snoc l n) = S (length l)

であることに注目する。これは\ ``l``\ についての帰納法から自明である。このとき、もとの性質についても\ ``l``\ についての帰納法から自明である。\ ``l = n'::l'``\ の場合については、上の性質と帰納法の仮定から導かれる。☐

どちらのスタイルの方が好ましいかは、読み手の証明への馴れや、彼らが今まで触れてきた証明がどちらに近いかに依ります。本書の目的としては冗長なスタイルの方が無難でしょう。

``SearchAbout``
~~~~~~~~~~~~~~~

これまで見てきたように、定理を証明するには既に証明した定理を使うことができます。以降では\ ``rewrite``\ 以外にも、証明済みの定理を使う方法があることを紹介します。ところで、定理を使うためにはその名前を知らなければなりませんが、使えそうな定理の名前をすべて覚えておくのはとても大変です。今まで証明した定理を覚えておくだけでも大変なのに、その名前となったら尚更です。

Coq
の\ ``SearchAbout``\ コマンドはこのような場合にとても便利です。\ ``SearchAbout foo``\ とすると、\ ``foo``\ に関する証明がすべて表示されます。例えば、次の部分のコメントを外せば、これまで\ ``rev``\ に関して証明した定理が表示されます。

続く練習問題やコースに取り組む際には、常に\ ``SearchAbout``\ コマンドのことを頭の隅に置いておくといいでしょう。そうすることでずいぶん時間の節約ができるはずです。

もし ProofGeneral
を使っているのなら、\ ``C-c C-f``\ とキー入力をすることで\ ``SearchAbout``\ コマンドを使うことができます。その結果をエディタに貼り付けるには\ ``C-c C-;``\ を使うことができます。

リストについての練習問題 (1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

練習問題: ★★★, recommended (list\_exercises)
''''''''''''''''''''''''''''''''''''''''''''

リストについてさらに練習しましょう。

::

    Theorem app_nil_end : forall l : natlist,
      l ++ [] = l.
    Proof.
      (* FILL IN HERE *) Admitted.


    Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
    Proof.
      (* FILL IN HERE *) Admitted.


    Theorem distr_rev : forall l1 l2 : natlist,
      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
    Proof.
      (* FILL IN HERE *) Admitted.

次の問題には簡単な解法があります。こんがらがってしまったようであれば、少し戻って単純な方法を探してみましょう。

::

    Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
    Proof.
      (* FILL IN HERE *) Admitted.

    Theorem snoc_append : forall (l:natlist) (n:nat),
      snoc l n = l ++ [n].
    Proof.
      (* FILL IN HERE *) Admitted.

前に書いた\ ``nonzeros``\ 関数に関する練習問題です。

::

    Lemma nonzeros_length : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
    Proof.
      (* FILL IN HERE *) Admitted.

☐

リストについての練習問題 (2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

練習問題: ★★, recommended (list\_design)
''''''''''''''''''''''''''''''''''''''''

自分で問題を考えましょう。

-  ``cons``\ （\ ``::``\ ）、\ ``snoc``\ 、\ ``append``\ （\ ``++``\ ）
   に関する、自明でない定理を考えて書きなさい。
-  それを証明しなさい。

   (\* FILL IN HERE \*)

☐

練習問題: ★★, optional (bag\_proofs)
''''''''''''''''''''''''''''''''''''

前のバッグについての optional
な練習問題に挑戦したのであれば、その定義について、以下の定理を証明しなさい。

::

    Theorem count_member_nonzero : forall (s : bag),
      ble_nat 1 (count 1 (1 :: s)) = true.
    Proof.
      (* FILL IN HERE *) Admitted.

以下の\ ``ble_nat``\ に関する補題は、この次の証明に使えるかもしれません。

::

    Theorem ble_n_Sn : forall n,
      ble_nat n (S n) = true.
    Proof.
      intros n. induction n as [| n'].
      Case "0".
        simpl.  reflexivity.
      Case "S n'".
        simpl.  rewrite IHn'.  reflexivity.  Qed.

    Theorem remove_decreases_count: forall (s : bag),
      ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

::

    (* Write down an interesting theorem about bags involving the
        functions [count] and [sum], and prove it.

練習問題: ★★★, optional (bag\_count\_sum)
'''''''''''''''''''''''''''''''''''''''''

バッグについて\ ``count``\ と\ ``sum``\ を使った定理を考え、それを証明しなさい。

::

    (* FILL IN HERE *)
    []
     *)

練習問題: ★★★★, optional (rev\_injective)
'''''''''''''''''''''''''''''''''''''''''

``rev``\ 関数が単射である、すなわち

::

        forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2

であることを証明しなさい。

この練習問題には簡単な解法と難しい解法があります。

::

    (* FILL IN HERE *)

☐

オプション
----------

次に、日々のプログラミングでも役に立つような型の定義を見てみましょう。

::

    Inductive natoption : Type :=
      | Some : nat -> natoption
      | None : natoption.

``natoption``\ 型の使い途のひとつは、関数からエラーコードを返すことです。例えば、リストの\ ``n``\ 番目の要素を返す関数を書きたいとしましょう。型を\ ``nat -> natlist -> nat``\ としてしまったら、リストが短かすぎた場合でも何か適当な数を返さなければなりません！

::

    Fixpoint index_bad (n:nat) (l:natlist) : nat :=
      match l with
      | nil => 42  
      | a :: l' => match beq_nat n O with
                   | true => a
                   | false => index_bad (pred n) l'
                   end
      end.

これに対して、型を\ ``nat -> natlist -> natoption``\ とすれば、リストが短かすぎた場合には\ ``None``\ を返し、リストが十分に長く、\ ``n``\ 番目の要素が\ ``a``\ であった場合には\ ``Some a``\ を返すことができます。

::

    Fixpoint index (n:nat) (l:natlist) : natoption :=
      match l with
      | nil => None
      | a :: l' => match beq_nat n O with
                   | true => Some a
                   | false => index (pred n) l'
                   end
      end.

    Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
    Proof. reflexivity.  Qed.
    Example test_index2 :    index 3 [4,5,6,7]  = Some 7.
    Proof. reflexivity.  Qed.
    Example test_index3 :    index 10 [4,5,6,7] = None.
    Proof. reflexivity.  Qed.

この機会に、 Coq
のプログラミング言語としての機能として、条件式を紹介しておきましょう。

::

    Fixpoint index' (n:nat) (l:natlist) : natoption :=
      match l with
      | nil => None
      | a :: l' => if beq_nat n O then Some a else index (pred n) l'
      end.

Coq
の条件式(if式)は他の言語に見られるものとほとんど同じですが、少しだけ一般化されています。
Coq には 組み込みのブーリアン型がないため、 Coq
の条件式では、実際には、構成子のふたつある任意の帰納型に対して分岐をすることができます。条件部の式が\ ``Inductive``\ の定義の最初の構成子に評価された場合には真、ふたつめの構成子に評価された場合には偽と見做されます。

次の関数は、\ ``natoption``\ 型から\ ``nat``\ の値を取り出し、\ ``None``\ の場合には与えられたデフォルト値を返します。

::

    Definition option_elim (o : natoption) (d : nat) : nat :=
      match o with
      | Some n' => n'
      | None => d
      end.

練習問題: ★★ (hd\_opt)
''''''''''''''''''''''

同じ考え方を使って、以前定義した\ ``hd``\ 関数を修正し、\ ``nil``\ の場合に返す値を渡さなくて済むようにしなさい。

::

    Definition hd_opt (l : natlist) : natoption :=
      (* FILL IN HERE *) admit.

    Example test_hd_opt1 : hd_opt [] = None.
     (* FILL IN HERE *) Admitted.

    Example test_hd_opt2 : hd_opt [1] = Some 1.
     (* FILL IN HERE *) Admitted.

    Example test_hd_opt3 : hd_opt [5,6] = Some 5.
     (* FILL IN HERE *) Admitted.

☐

練習問題: ★★, optional (option\_elim\_hd)
'''''''''''''''''''''''''''''''''''''''''

新しい\ ``hd_opt``\ と古い\ ``hd``\ の関係についての練習問題です。

::

    Theorem option_elim_hd : forall (l:natlist) (default:nat),
      hd default l = option_elim (hd_opt l) default.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★, recommended (beq\_natlist)
''''''''''''''''''''''''''''''''''''''''

数のリストふたつを比較し等価性を判定する関数\ ``beq_natlist``\ の定義を完成させなさい。そして、\ ``beq_natlist l l``\ が任意のリスト\ ``l``\ で\ ``true``\ となることを証明しなさい。

::

    Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
      (* FILL IN HERE *) admit.

    Example test_beq_natlist1 :   (beq_natlist nil nil = true).
     (* FILL IN HERE *) Admitted.
    Example test_beq_natlist2 :   beq_natlist [1,2,3] [1,2,3] = true.
     (* FILL IN HERE *) Admitted.
    Example test_beq_natlist3 :   beq_natlist [1,2,3] [1,2,4] = false.
     (* FILL IN HERE *) Admitted.

    Theorem beq_natlist_refl : forall l:natlist,
      true = beq_natlist l l.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

``apply``\ タクティック
-----------------------

証明をしていると、証明すべきゴールがコンテキスト中の仮定と同じであったり以前証明した補題と同じであることがしばしばあります。

::

    Theorem silly1 : forall (n m o p : nat),
         n = m  ->
         [n,o] = [n,p] ->
         [n,o] = [m,p].
    Proof.
      intros n m o p eq1 eq2.
      rewrite <- eq1.


      apply eq2.  Qed.

また、\ ``apply``\ タクティックは、条件付きの仮定や補題にも使うことができます。適用するものに含意が含まれていれば、含意の前提部分が証明すべきサブゴールに加えられます。

::

    Theorem silly2 : forall (n m o p : nat),
         n = m  ->
         (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
         [n,o] = [m,p].
    Proof.
      intros n m o p eq1 eq2.
      apply eq2. apply eq1.  Qed.

この証明で、\ ``apply``\ の代わりに\ ``rewrite``\ を使って証明を終えられるか試してみると有益でしょう。

``apply H``\ を使う典型的な例は、\ ``H``\ が\ ``forall``\ で始まり、何らかの全称限量された変数を束縛している場合です。現在のゴールが\ ``H``\ の帰結部と一致した場合には、変数に対応する適当な値を見つけてくれます。例えば、次の証明で\ ``apply eq2``\ すると、\ ``eq2``\ 内の変数\ ``q``\ は\ ``n``\ に、\ ``r``\ は\ ``m``\ に具体化されます。

::

    Theorem silly2a : forall (n m : nat),
         (n,n) = (m,m)  ->
         (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
         [n] = [m].
    Proof.
      intros n m eq1 eq2.
      apply eq2. apply eq1.  Qed.

練習問題: ★★, optional (silly\_ex)
''''''''''''''''''''''''''''''''''

次の証明を\ ``simpl``\ を使わずに完成させなさい。

::

    Theorem silly_ex :
         (forall n, evenb n = true -> oddb (S n) = true) ->
         evenb 3 = true ->
         oddb 4 = true.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

``apply``\ タクティックを使う場合には、適用する事実（の帰結部）が、ゴールと完全に一致していなければなりません。例えは、等式の左辺と右辺が入れ替わっているだけでも\ ``apply``\ タクティックは使えません。

::

    Theorem silly3_firsttry : forall (n : nat),
         true = beq_nat n 5  ->
         beq_nat (S (S n)) 7 = true.
    Proof.
      intros n H.
      simpl.


    Admitted.

そのような場合には\ ``symmetry``\ タクティックを使って、ゴールの等式の左辺と右辺を入れ替えることができます。

::

    Theorem silly3 : forall (n : nat),
         true = beq_nat n 5  ->
         beq_nat (S (S n)) 7 = true.
    Proof.
      intros n H.
      symmetry.
      simpl.   

      apply H.  Qed.

練習問題: ★★★, recommended (apply\_exercise1)
'''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem rev_exercise1 : forall (l l' : natlist),
         l = rev l' ->
         l' = rev l.
    Proof.


      (* FILL IN HERE *) Admitted.

FILL IN HERE ☐

練習問題: ★ (apply\_rewrite)
''''''''''''''''''''''''''''

``apply``\ と\ ``rewrite``\ の違いを簡単に説明しなさい。どちらもうまく使えるような場面はありますか？

(\* FILL IN HERE \*)

☐

帰納法の仮定を変更する
----------------------

帰納法による証明の微妙さについては説明しておく価値があるでしょう。例えば、以前証明した\ ``app_ass``\ を見てみましょう。帰納法の仮定（\ ``induction``\ タクティックで生成されたふたつめのサブゴール）は以下のようなものでした。

``(l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3``

（\ ``++``\ を右結合と定義したので、\ ``=``\ の右辺は\ ``l1' ++ (l2 ++ l3)``\ と同じです。）

この仮定は、\ ``l1'``\ と、特定のリスト\ ``l2``\ 、\ ``l3``\ に関するものです。\ ``l2``\ と\ ``l3``\ はこの証明の初めに\ ``intros``\ タクティックで導入したもので、この仮定中で「一定」です。証明の方法を少し変えて、最初に\ ``n``\ だけをコンテキストに\ ``intros``\ するようにしたら、帰納法の仮定は次のようにもっと強いものになります。

``forall l2 l3,  (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3``

Coq を使って実際に違いを確認してください。

今回の場合では、ふたつの証明の違いはささいものです。これは、\ ``++``\ 関数の定義が最初の引数だけを見て、ふたつめの引数には特に何もしないからです。しかし、遠からずわかることですが、帰納法の仮定をどちらにするかで証明の成否が分かれることもあるのです。

練習問題: ★★, optional (app\_ass')
''''''''''''''''''''''''''''''''''

``++``\ の結合則をより一般的な仮定のもとで証明しなさい。（最初の行を変更せずに）次の証明を完成させること。

::

    Theorem app_ass' : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
    Proof.
      intros l1. induction l1 as [ | n l1'].
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★ (apply\_exercise2)
''''''''''''''''''''''''''''''''

``induction``\ の前に\ ``m``\ を\ ``intros``\ していないことに注意してください。これによって仮定が一般化され、帰納法の仮定が特定の\ ``m``\ に縛られることがなくなり、より使いやすくなりました。

::

    Theorem beq_nat_sym : forall (n m : nat),
      beq_nat n m = beq_nat m n.
    Proof.
      intros n. induction n as [| n'].
      (* FILL IN HERE *) Admitted.

☐

::

    []
     *)

FILL IN HERE ##### 練習問題: ★★★, recommended (beq\_nat\_sym\_informal)

以下の補題について上の証明と対応する非形式的な証明を書きなさい。

定理:
任意の\ ``nat``n``m``\ について、\ ``beq_nat n m = beq_nat m n``\ 。

証明:(\* FILL IN HERE \*)☐

::

    End NatList.

練習問題: 辞書
--------------

::

    Module Dictionary.

    Inductive dictionary : Type :=
      | empty  : dictionary
      | record : nat -> nat -> dictionary -> dictionary.

この宣言は次のように読めます。「\ ``dictionary``\ を構成する方法はふたつある。構成子\ ``empty``\ で空の辞書を表現するか、構成子\ ``record``\ をキーと値と既存の\ ``dictionary``\ に適用してキーと値の対応を追加した\ ``dictionary``\ を構成するかのいずれかである」。

::

    Definition insert (key value : nat) (d : dictionary) : dictionary :=
      (record key value d).

下の\ ``find``\ 関数は、\ ``dictionary``\ から与えられたキーに対応する値を探し出すものです。
キーが見つからなかった場合には\ ``None``\ に評価され、キーが\ ``val``\ に結び付けられていた場合には\ ``Some val``\ に評価されます。同じキーが複数の値に結び付けられている場合には、最初に見つかったほうの値を返します。

::

    Fixpoint find (key : nat) (d : dictionary) : option nat :=
      match d with
      | empty         => None
      | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
      end.

練習問題: ★ (dictionary\_invariant1)
''''''''''''''''''''''''''''''''''''

::

    Theorem dictionary_invariant1 : forall (d : dictionary) (k v: nat),
      (find k (insert k v d)) = Some v.
    Proof.
     (* FILL IN HERE *) Admitted.

☐

練習問題: ★ (dictionary\_invariant2)
''''''''''''''''''''''''''''''''''''

::

    Theorem dictionary_invariant2 : forall (d : dictionary) (m n o: nat),
      (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
    Proof.
     (* FILL IN HERE *) Admitted.

☐

::

    End Dictionary.

次の宣言で、\ ``beq_nat_sym``\ の定義をトップレベルの名前空間に置いておきます。こうすることで、後で\ ``beq_nat_sym``\ を使うのに\ ``NatList.beq_nat_sym``\ と書かずに済みます。

::

    Definition beq_nat_sym := NatList.beq_nat_sym.

