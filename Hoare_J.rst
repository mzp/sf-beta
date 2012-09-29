Hoare\_J: ホーア論理
====================

::

    /\ verification_conditions P' c
       His full development (based on an old version of our formalized
       decorated programs, unfortunately), can be found in the file
       /underconstruction/PilkiewiczFormalizedDecorated.v *)

                             /\ verification_conditions P' c
       彼の完全版(残念ながら、我々の修飾付きプログラムの古いバージョンをベースにしている)は
       以下のファイルにある。
       /underconstruction/PilkiewiczFormalizedDecorated.v *)

    Require Export ImpList_J.

コースの最初のパートで用意した数学的道具立てを、小さなプログラミング言語
Imp の理論の学習に適用し始めています。

-  Imp の抽象構文木(*abstract syntax trees*)の型を定義しました。
   また、操作的意味論(*operational
   semantics*)を与える評価関係(*evaluation
   relation*\ 、状態間の部分関数)も定義しました。定義した言語は小さいですが、C,
   C++, Java
   などの本格的な言語の主要な機能を持っています。その中には変更可能な状態や、いくつかのよく知られた制御構造も含まれます。

-  いくつものメタ理論的性質(*metatheoretic properties*)を証明しました。
   "メタ"というのは、言語で書かれた特定のプログラムの性質ではなく言語自体の性質という意味です。証明したものには、以下のものが含まれます:

   -  評価の決定性
   -  異なった書き方をした定義の同値性
   -  プログラムのあるクラスの、停止性の保証
   -  プログラムの動作の同値性(``Equiv_J.v``\ のオプションの章において)
      もしここで止めたとしても、有用なものを持っていることになります。それは、プログラミング言語とその特性を定義し議論する、数学的に正確で、柔軟で、使いやすい、主要な性質に適合した道具立てです。
      これらの性質は、言語を設計する人、コンパイラを書く人、そしてユーザも知っておくべきものです。実際、その多くは我々が扱うプログラミング言語を理解する上で本当に基本的なことですので、"定理"と意識することはなかったかもしれません。しかし、直観的に明らかだと思っている性質はしばしばとても曖昧で、時には間違っていることもあります!
      この問題については、後に型(*types*)とその健全性(*type
      soundness*)を議論する際に再度出てきます。

-  プログラムの検証(*program verification*)の例を2つ行いました。 Imp
   を厳密に定義し、ある特定のプログラム(つまり階乗計算と遅い引き算)がその動作についての特定の仕様を満たすことを、形式的に証明するものでした。

この章では、この最後の考え方をさらに進めます。一般にフロイド-ホーア論理(*Floyd-Hoare
Logic*)、あるいは、少々不公平に省略してホーア論理(*Hoare
Logic*)と呼ばれている推論システムを作ります。この推論システムの中では、Imp
の各構文要素に対して1つの一般的な"証明規則"(proof
rule)が与えられ、これによってその構文要素を含むプログラムについての推論ができるようになっています。

ホーア論理の起源は1960年代です。そして今現在まで継続してさかんに研究がされています。実際のソフトウェアシステムの仕様を定め検証するために使われている非常に多くのツールは、ホーア論理を核としているのです。

ホーア論理
----------

ホーア論理は2つの重要なことがらを提供します。プログラムの仕様(*specification*)を自然に記述する方法と、その仕様が適合していることを証明する合成的証明法(*compositionalproof
technique*)です。ここでの"合成的"(compositional)という意味は、証明の構造が証明対象となるプログラムの構造を直接的に反映しているということです。

表明
~~~~

プログラムの仕様について話そうとするとき、最初に欲しくなるのは、ある特定の時点で成立している性質
-- つまり、与えられたメモリ状態で真になり得るか、なり得ないかの性質 --
についての表明(*assertions*)を作る方法です。

::

    Definition Assertion := state -> Prop.

練習問題: ★ (assertions)
''''''''''''''''''''''''

以下の表明を日本語に直しなさい。

::

          fun st =>  asnat (st X) = 3
          fun st =>  asnat (st X) = x
          fun st =>  asnat (st X) <= asnat (st Y)
          fun st =>  asnat (st X) = 3 \/ asnat (st X) <= asnat (st Y)
          fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x 
                     /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x)
          fun st =>  True
          fun st =>  False

☐

この方法で表明を書くことは、形式的に正しいのです。

-  

   -  この方法は意図することを正確におさえています。

そしてこれがまさに Coq
の証明で使う方法なのです。しかしこれはいくつかの理由から、若干ヘビーに見えます。(1)すべての個々の表明は、\ ``fun st=>``\ から始まっています。(2)状態\ ``st``\ は変数を参照するために使うただ1つのものです(2つの別々の状態を同時に考える必要はありません)。(3)表明で参照するすべての変数は\ ``asnat``\ または\ ``aslist``\ の強制型変換により、取り散らかっています。表明を非形式的に書くときには、いくらか簡単にします。最初の\ ``fun st =>``\ は書かず、\ ``st X``\ のかわりに単に\ ``X``\ と書きます。また\ ``asnat``\ と\ ``aslist``\ は略します。

非形式的には、次のように書くかわりに

::

          fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x 
                     /\ ~ ((S (asnat (st Z))) * (S (asnat (st Z))) <= x)

次のように書きます。

::

             Z * Z <= x 
          /\ ~((S Z) * (S Z) <= x).

ホーアの三つ組
~~~~~~~~~~~~~~

次に、コマンドの振舞いの仕様を定める、つまりコマンドの振舞いについての表明を作る方法が必要です。

表明を、状態の性質について表明するものとして定義してきました。そして、コマンドの振舞いは、状態を別の状態に変換するものです。これから、コマンドについての表明は次の形をとります:

-  "もし\ ``c``\ が表明\ ``P``\ を満たす状態から開始され、また、\ ``c``\ がいつかは停止するならば、最終状態では、表明\ ``Q``\ が成立することを保証する。"

この表明は ホーアの三つ組(*Hoare
Triple*)と呼ばれます。性質\ ``P``\ は\ ``c``\ の事前条件(*precondition*)と呼ばれます。\ ``Q``\ は\ ``c``\ の事後条件(*postcondition*)と呼ばれます。

(伝統的に、ホーアの三つ組は\ ``{P} c {Q}``\ と書かれます。しかし Coq
では一重の中カッコは別の意味で既に使われています。)

::

    Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
      forall st st',
           c / st || st'  ->
           P st  ->
           Q st'.

ホーアの三つ組を今後多用するので、簡潔な記法を用意すると便利です:

::

           {{P}}  c  {{Q}}.

    Notation "{{ P }}  c" :=          (hoare_triple P c (fun st => True)) (at level 90)
                                      : hoare_spec_scope.
    Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level)
                                      : hoare_spec_scope.
    Open Scope hoare_spec_scope.

この\ ``hoare_spec_scope``\ アノテーションは、Coqに、この記法はグローバルではなく特定のコンテキストで使うものであることを伝えるものです。\ ``Open Scope``\ は、このファイルがそのコンテキストであることを
Coq
に伝えます。最初の、事後条件を持たない記法は、ここで実際に使うことはありません。これは単に後に定義する記法のための場所を用意したものです。後に修飾付きプログラムについて議論する際に使います。

練習問題: ★ (triples)
'''''''''''''''''''''

以下のホーアの三つ組を日本語に直しなさい。

::

          {{True}} c {{X = 5}}

          {{X = x}} c {{X = x + 5)}}

          {{X <= Y}} c {{Y <= X}}

          {{True}} c {{False}}

          {{X = x}}
          c
          {{Y = real_fact x}}.

          {{True}}
          c
          {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}

☐

練習問題: ★ (valid\_triples)
''''''''''''''''''''''''''''

以下のホーアの三つ組のうち、正しい(*valid*)ものを選択しなさい。

-  

   -  正しいとは、\ ``P``,\ ``c``,\ ``Q``\ の関係が真であるということです。

      {{True}} X ::= 5 {{X = 5}}

      {{X = 2}} X ::= X + 1 {{X = 3}}

      {{True}} X ::= 5; Y ::= 0 {{X = 5}}

      {{X = 2 / X = 3}} X ::= 5 {{X = 0}}

      {{True}} SKIP {{False}}

      {{False}} SKIP {{True}}

      {{True}} WHILE True DO SKIP END {{False}}

      {{X = 0}} WHILE X == 0 DO X ::= X + 1 END {{X = 1}}

      {{X = 1}} WHILE X <> 0 DO X ::= X + 1 END {{X = 100}}

(読みやすくするため、コマンド内の式について、非形式的な数学記法を使います。この章の最後までその方針をとります。)

☐

ウォーミングアップとして、ホーアの三つ組についての2つの事実を見てみます。

::

    Theorem hoare_post_true : forall (P Q : Assertion) c,
      (forall st, Q st) ->
      {{P}} c {{Q}}.
    Proof.
      intros P Q c H. unfold hoare_triple.
      intros st st' Heval HP.
      apply H.  Qed.

    Theorem hoare_pre_false : forall (P Q : Assertion) c,
      (forall st, ~(P st)) ->
      {{P}} c {{Q}}.
    Proof.
      intros P Q c H. unfold hoare_triple.
      intros st st' Heval HP.
      unfold not in H. apply H in HP.
      inversion HP.  Qed.

最弱事前条件
~~~~~~~~~~~~

いくつかの ホーアの三つ組は、他のものより興味深いものです。例えば:

::

          {{ False }}  X ::= Y + 1  {{ X <= 5 }}

はあまり興味深いものではありません。これは完全に正しいものですが、何も有用なことを伝えてくれません。事前条件がどのような状態でも満たされないことから、コマンド\ ``X ::= Y + 1``\ によって事後条件\ ``X <= 5``\ に至るどのような状況も記述していません。一方、

::

          {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}

は有用です。これは、何らかの方法で\ ``Y <= 4 /\ Z = 0``\ であるという状況を作りあげた後、このコマンドを実行すると事後条件を満たす状態になる、ということを伝えています。しかしながら、この三つ組はもう少し改良できます。なぜなら、事前条件の\ ``Z = 0``\ という節は、実際には事後条件\ ``X <= 5``\ に何の影響も与えないからです。(このコマンドと事後条件のもとで)最も有効な三つ組は次のものです:

::

          {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}

言いかえると、\ ``Y <= 4``\ は事後条件\ ``X <= 5``\ に対してコマンド\ ``X ::= Y + 1``\ の最弱の(*weakest*)正しい事前条件です。

一般に、次が成立するとき"``P``\ は\ ``Q``\ に対する\ ``c``\ の最弱事前条件である"と言います:

-  ``{{P}} c {{Q}}``, かつ
-  ``P'``\ が\ ``{{P'}} c {{Q}}``\ を満たす表明ならば,
   すべての状態\ ``st``\ について、\ ``P' st``\ ならば\ ``P st``\ となる。

つまり、\ ``P``\ が\ ``Q``\ に対する\ ``c``\ の最弱事前条件であるとは、(a)\ ``P``\ は\ ``Q``\ と\ ``c``\ の事前条件で、かつ、(b)\ ``P``\ は\ ``c``\ の後で\ ``Q``\ を保証する最弱の(*weakest*)(もっとも簡単に充足できる)表明である、ということです。

練習問題: ★ (wp)
''''''''''''''''

以下のコマンドの以下の事後条件に対する最弱事前条件を示しなさい。

::

         {{ ? }}  SKIP  {{ X = 5 }}

         {{ ? }}  X ::= Y + Z {{ X = 5 }}

         {{ ? }}  X ::= Y  {{ X = Y }}

         {{ ? }}
         IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
         {{ Y = 5 }}

         {{ ? }}
         X ::= 5
         {{ X = 0 }}

         {{ ? }}
         WHILE True DO X ::= 0 END
         {{ X = 0 }}

☐

証明規則
~~~~~~~~

ホーア論理のゴールは、ホーアの三つ組の正しさを証明する"合成的"手法を提供することです。つまり、プログラムの正しさの証明の構造は、プログラムの構造をそのまま反映したものになるということです。このゴールのために、以降の節では、Impのコマンドのいろいろな構文要素のそれぞれ対して、その構文要素について推論するための規則を1つずつ導入します。代入に1つ、コマンド合成に1つ、条件分岐に1つ、等です。それに加えて、複数のものを結合するために有用な2つの"構造的"規則を導入します。

代入
^^^^

代入の規則は、ホーア論理の証明規則の中で最も基本的なものです。この規則は次のように働きます。

次の(正しい)ホーアの三つ組を考えます。

::

           {{ Y = 1 }}  X ::= Y  {{ X = 1 }}

日本語で言うと、\ ``Y``\ の値が\ ``1``\ である状態から始めて、\ ``X``\ を\ ``Y``\ に代入するならば、\ ``X``\ が\ ``1``\ である状態になる、ということです。つまり、\ ``1``\ である、という性質が\ ``X``\ から\ ``Y``\ に移された、ということです。

同様に、

::

           {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}

においては、同じ性質(1であること)が代入の右辺の\ ``Y+Z``\ から\ ``X``\ に移動されています。

より一般に、\ ``a``\ が「任意の」算術式のとき、

::

           {{ a = 1 }}  X ::= a {{ X = 1 }}

は正しいホーアの三つ組になります。

さらに一般化して、\ ``a``\ が「任意の」算術式、\ ``Q``\ が数についての「任意の」性質のとき、

::

           {{ Q(a) }}  X ::= a {{ Q(X) }}

は正しいホーアの三つ組です。

これを若干言い換えると、代入に対する一般ホーア規則になります:

::

          {{ Q において X を a で置換したもの }}  X ::= a  {{ Q }}

例えば、以下は、代入規則の正しい適用です:

::

          {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}

          {{ 3 = 3 }}  X ::= 3  {{ X = 3 }}

          {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

``Q``\ を、算術式をインデックスとする表明の族として扱うことで、代入規則を
Coq で直接形式化してみることもできます。例えば次のようになります。

::

          Theorem hoare_asgn_firsttry :
            forall (Q : aexp -> Assertion) V a,
            {{fun st => Q a st}} (V ::= a) {{fun st => Q (AId V) st}}.

しかし、この形式化は2つの理由であまり良くないのです。第一に、この式は本当に正しいとは言えないのです!(反例として、\ ``Q``\ として自分の引数の「構文」を調べるものを考えてみましょう。次のようなものです:

::

        Definition Q (a:aexp) : Prop :=
           match a with
           | AID (Id 0) => fun st => False
           | _          => fun st => True
           end.

このとき、代入として、\ ``V = Id 0``\ を考えると、事前条件は\ ``True``\ となりますが、事後条件は\ ``False``\ になります。)第二の理由は、たとえ同様のことが証明できたとしても、これは使いにくいのです。

規則を形式化するはるかにスムーズな方法は、以下の洞察から得られます:

-  "``Q``\ において\ ``X``\ を a
   で置換したもの"が状態\ ``st``\ で成立する必要十分条件は、\ ``Q``\ が状態\ ``update st X (aeval st a)``\ で成立することである。

つまり、ある状態で、\ ``Q``\ を置換してできるものを表明することは、その状態を置換してできる状態で、\ ``Q``\ を表明することと同じだということです。

状態の置換を次のように定義します:

::

    Definition assn_sub V a Q : Assertion :=
      fun (st : state) =>
        Q (update st V (aeval st a)).

これを使って、代入の証明規則を形式的に与えます:

::

          ------------------------------ (hoare_asgn)
          {{assn_sub V a Q}} V::=a {{Q}}

    Theorem hoare_asgn : forall Q V a,
      {{assn_sub V a Q}} (V ::= a) {{Q}}.
    Proof.
      unfold hoare_triple.
      intros Q V a st st' HE HQ.
      inversion HE. subst.
      unfold assn_sub in HQ. assumption.  Qed.

この規則を使った最初の形式的証明が次のものです。

::

    Example assn_sub_example :
      {{fun st => 3 = 3}}
      (X ::= (ANum 3))
      {{fun st => asnat (st X) = 3}}.
    Proof.
      assert ((fun st => 3 = 3) =
              (assn_sub X (ANum 3) (fun st => asnat (st X) = 3))).
      Case "Proof of assertion".
        unfold assn_sub. reflexivity.
      rewrite -> H. apply hoare_asgn.  Qed.

この証明はあまり綺麗ではありません。なぜなら、\ ``hoare_asgn``\ 規則が最初のゴールに直接適用されてはいないからです。この規則は、事前条件が、何らかの\ ``Q``\ 、\ ``V``\ 、\ ``a``\ について\ ``assn_sub Q V a``\ という形をしているときのみに適用できます。このため、ゴールをこの形にするためのちょっとした補題から始めなければならないのです。

``hoare_asgn``\ を使おうとするときに、毎回ゴール状態に対してこのような小細工をするのは面倒です。幸い、より簡単な方法があります。その一つは、明示的な等式の形の仮定を導く、いくらか一般性の高い定理を示すことです:

::

    Theorem hoare_asgn_eq : forall Q Q' V a,
         Q' = assn_sub V a Q ->
         {{Q'}} (V ::= a) {{Q}}.
    Proof.
      intros Q Q' V a H. rewrite H. apply hoare_asgn.  Qed.

``hoare_asgn``\ のこのバージョンを使うことで、証明をよりスムーズに行うことができます。

::

    Example assn_sub_example' :
      {{fun st => 3 = 3}}
      (X ::= (ANum 3))
      {{fun st => asnat (st X) = 3}}.
    Proof.
      apply hoare_asgn_eq. reflexivity.  Qed.

練習問題: ★★ (hoare\_asgn\_examples)
''''''''''''''''''''''''''''''''''''

次の非形式的なホーアの三つ組...

::

           {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
           {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

...を、形式的記述に直し、\ ``hoare_asgn_eq``\ を使って証明しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: ★★★ (hoarestate2)
'''''''''''''''''''''''''''

::

    *)

FILL IN HERE
代入規則は、最初に見たとき、ほとんどの人が後向きの規則であるように感じます。もし今でも後向きに見えるならば、前向きバージョンの規則を考えてみるのも良いかもしれません。次のものは自然に見えます:

::

          {{ True }} X ::= a {{ X = a }}

この規則の問題点を指摘しなさい。

(\* FILL IN HERE \*)

☐

練習問題: ★★★, optional (hoare\_asgn\_weakest)
''''''''''''''''''''''''''''''''''''''''''''''

``hoare_asgn``\ 規則の事前条件が、本当に最弱事前条件であることを示しなさい。

::

    Theorem hoare_asgn_weakest : forall P V a Q,
      {{P}} (V ::= a) {{Q}} ->
      forall st, P st -> assn_sub V a Q st.
    Proof.
    (* FILL IN HERE *) Admitted.

☐

帰結
^^^^

代入規則の適用のぎこちなさに関する上記の議論は、より一般的なポイントを示しています。ホーア規則から得られる事前条件と事後条件は欲しいものではないことがしばしばあるのです。(上の例のように)それらは論理的に同値ですが、構文的に違う形をしているために、証明しようと思うゴールと単一化することができないのです。あるいは、(事前条件について)必要なものより論理的に弱かったり、(事後条件について)論理的に強かったりするのです。

例えば、

::

          {{3 = 3}} X ::= 3 {{X = 3}},

が代入規則に直接従うのに対して、より自然な三つ組

::

          {{True}} X ::= 3 {{X = 3}}.

はそうではないのです。この三つ組も正しいのですが、\ ``hoare_asgn``\ (または\ ``hoare_asgn_eq``)
のインスタンスではないのです。なぜなら、\ ``True``\ と\ ``3 = 3``\ は、構文的に等しい表明ではないからです。

一般に、\ ``{{P}} c {{Q}}``\ が導出できるとき、\ ``P'``\ ならば\ ``P``\ が言えるだけ\ ``P'``\ が十分強ければ、\ ``P``\ を\ ``P'``\ に置き換えることは正しく、また\ ``Q``\ ならば\ ``Q'``\ が言えるときには、\ ``Q``\ を\ ``Q'``\ に置き換えることは正しいのです。

この洞察をまとめたものが、次の帰結規則(*Rule of Consequence*)です。

::

                    {{P'}} c {{Q'}}
             P implies P' (in every state)
             Q' implies Q (in every state)
             -----------------------------  (hoare_consequence)
                    {{P}} c {{Q}}

便宜上、さらに2つの帰結規則を用意します。1つは事前条件を強めるだけのもの、もう1つは事後条件を弱めるだけのものです。

::

                    {{P'}} c {{Q}}
             P implies P' (in every state)
             -----------------------------   (hoare_consequence_pre)
                    {{P}} c {{Q}}

                    {{P}} c {{Q'}}
             Q' implies Q (in every state)
             -----------------------------    (hoare_consequence_post)
                    {{P}} c {{Q}}

以下が形式化版です:

::

    Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
      {{P'}} c {{Q'}} ->
      (forall st, P st -> P' st) ->
      (forall st, Q' st -> Q st) ->
      {{P}} c {{Q}}.
    Proof.
      intros P P' Q Q' c Hht HPP' HQ'Q.
      intros st st' Hc HP.
      apply HQ'Q.  apply (Hht st st'). assumption.
      apply HPP'. assumption.  Qed.

    Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
      {{P'}} c {{Q}} ->
      (forall st, P st -> P' st) ->
      {{P}} c {{Q}}.
    Proof.
      intros P P' Q c Hhoare Himp.
      apply hoare_consequence with (P' := P') (Q' := Q);
        try assumption.
      intros st H. apply H.  Qed.

    Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
      {{P}} c {{Q'}} ->
      (forall st, Q' st -> Q st) ->
      {{P}} c {{Q}}.
    Proof.
      intros P Q Q' c Hhoare Himp.
      apply hoare_consequence with (P' := P) (Q' := Q');
        try assumption.
      intros st H. apply H.  Qed.

(例えば、("``_pre``\ "版の)帰結規則を次のように使うことができます:

::

                    {{ True }} =>
                    {{ 1 = 1 }}
        X ::= 1
                    {{ X = 1 }}

あるいは、形式化すると...

::

    Example hoare_asgn_example1 :
      {{fun st => True}} (X ::= (ANum 1)) {{fun st => asnat (st X) = 1}}.
    Proof.
      apply hoare_consequence_pre with (P' := (fun st => 1 = 1)).
      apply hoare_asgn_eq. reflexivity.
      intros st H. reflexivity.  Qed.

余談:``eapply``\ タクティック
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

ここで、良い機会ですので、Coq
の別の便利な機能を紹介しておきましょう。上述の例で明示的に\ ``P'``\ を書かなければならないことは、少々やっかいです。なぜなら、すぐ次にやること、つまり\ ``hoare_asgn``\ 規則を適用すること、が、まさに、それがどうでなければならないかを決定することだからです。こういう場合、\ ``apply``\ の代わりに\ ``eapply``\ を使うことができます。そうすることは、本質的に、「抜けている部分は後で埋めます」とCoq
に伝えることになります。

::

    Example hoare_asgn_example1' :
      {{fun st => True}}
      (X ::= (ANum 1))
      {{fun st => asnat (st X) = 1}}.
    Proof.
      eapply hoare_consequence_pre.
      apply hoare_asgn_eq. reflexivity. 
      intros st H. reflexivity.  Qed.

一般に、\ ``eapply H``\ タクティックは\ ``apply H``\ とほぼ同様にはたらきますが、次の点が違います。\ ``H``\ の結論部とゴールとの単一化では\ ``H``\ の前提部に現れる変数のすべてが具体化されなかった場合、\ ``apply H``\ は失敗しますが、\ ``eapply H``\ は残った変数を存在変数(*existential
variables*\ 、\ ``?nnn``\ と記述される)に置換します。存在変数は、証明の以降の部分で(さらなる単一化により)決定される式が入る場所を示すものです。

他に同様のはたらきをするものには、\ ``eassumption``\ タクティックがあります。

Skip
^^^^

``SKIP``\ は状態を変えないことから、任意の性質 P を保存します:

::

          --------------------  (hoare_skip)
          {{ P }} SKIP {{ P }}

    Theorem hoare_skip : forall P,
         {{P}} SKIP {{P}}.
    Proof.
      intros P st st' H HP. inversion H. subst.
      assumption.  Qed.

コマンド合成
^^^^^^^^^^^^

より興味深いことに、コマンド\ ``c1``\ が、\ ``P``\ が成立する任意の状態を\ ``Q``\ が成立する状態にし、\ ``c2``\ が、\ ``Q``\ が成立する任意の状態を\ ``R``\ が成立する状態にするとき、\ ``c1``\ に続いて\ ``c2``\ を行うことは、\ ``P``\ が成立する任意の状態を\ ``R``\ が成立する状態にします:

::

            {{ P }} c1 {{ Q }}
            {{ Q }} c2 {{ R }}
           ---------------------  (hoare_seq)
           {{ P }} c1;c2 {{ R }}

    Theorem hoare_seq : forall P Q R c1 c2,
         {{Q}} c2 {{R}} ->
         {{P}} c1 {{Q}} ->
         {{P}} c1;c2 {{R}}.
    Proof.
      intros P Q R c1 c2 H1 H2 st st' H12 Pre.
      inversion H12; subst.
      apply (H1 st'0 st'); try assumption.
      apply (H2 st st'0); try assumption. Qed.

形式的規則\ ``hoare_seq``\ においては、前提部分が「逆順」である(``c1``\ の前に\ ``c2``\ が来る)ことに注意してください。この順は、規則を使用する多くの場面で情報の自然な流れにマッチするのです。

非形式的には、この規則を利用した証明を記録する良い方法は、\ ``c1``\ と\ ``c2``\ の間に中間表明\ ``Q``\ を記述する"修飾付きプログラム"の様にすることです:

::

          {{ a = n }}
        X ::= a;
          {{ X = n }}      <---- 修飾 Q
        SKIP
          {{ X = n }}

    Example hoare_asgn_example3 : forall a n,
      {{fun st => aeval st a = n}}
      (X ::= a; SKIP)
      {{fun st => st X = n}}.
    Proof.
      intros a n. eapply hoare_seq.
      Case "right part of seq".
        apply hoare_skip.
      Case "left part of seq".
        eapply hoare_consequence_pre. apply hoare_asgn.
        intros st H.  subst.  reflexivity. Qed.

練習問題: ★★ (hoare\_asgn\_example4)
''''''''''''''''''''''''''''''''''''

次の修飾付きプログラムを形式的証明に直しなさい:

::

                       {{ True }} =>
                       {{ 1 = 1 }}
        X ::= 1;
                       {{ X = 1 }} =>
                       {{ X = 1 /\ 2 = 2 }}
        Y ::= 2
                       {{ X = 1 /\ Y = 2 }}

    Example hoare_asgn_example4 :
      {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2))
      {{fun st => asnat (st X) = 1 /\ asnat (st Y) = 2}}.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★, optional (swap\_exercise)
''''''''''''''''''''''''''''''''''''''''

``X``\ と\ ``Y``\ の値を交換するImpプログラム\ ``c``\ を書き、それが次の仕様を満たすことを(Coq
で)示しなさい:

::

          {{X <= Y}} c {{Y <= X}}

    (* FILL IN HERE *)

☐

練習問題: ★★★, optional (hoarestate1)
'''''''''''''''''''''''''''''''''''''

次の命題が証明できない理由を説明しなさい:

::

          forall (a : aexp) (n : nat),
             {{fun st => aeval st a = n}} (X ::= (ANum 3); Y ::= a)
             {{fun st => asnat (st Y) = n}}.

    (* FILL IN HERE *)

☐

条件分岐
^^^^^^^^

条件分岐コマンドについて推論するために、どのような規則が必要でしょうか？確かに、分岐のどちらの枝を実行した後でも表明\ ``Q``\ が成立するならば、条件分岐全体でも\ ``Q``\ が成立するでしょう。これから次のように書くべきかもしれません:

::

                  {{P}} c1 {{Q}}
                  {{P}} c2 {{Q}}
          --------------------------------
          {{P}} IFB b THEN c1 ELSE c2 {{Q}}

しかし、これはかなり弱いのです。例えば、この規則を使っても次のことを示すことができません:

::

         {{True}}
         IFB X == 0
         THEN Y ::= 2
         ELSE Y ::= X + 1
         FI
         {{ X <= Y }}

なぜなら、この規則では、"then"部と"else"部のどちらの代入が起こる状態なのかについて、何も言っていないからです。

しかし、実際には、より詳しいことを言うことができます。"then"の枝では、ブール式\ ``b``\ の評価結果が\ ``true``\ になることがわかっています。また"else"の枝では、それが\ ``false``\ になることがわかっています。この情報を補題の前提部分で利用できるようにすることで、\ ``c1``\ と\ ``c2``\ の振舞いについて(つまり事後条件\ ``Q``\ が成立する理由について)推論するときに、より多くの情報を使うことができるようになります。

::

                  {{P /\  b}} c1 {{Q}}
                  {{P /\ ~b}} c2 {{Q}}
          ------------------------------------  (hoare_if)
          {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}

この規則を形式的に解釈するために、もう少しやることがあります。

厳密には、上述の表明において、表明とブール式の連言\ ``P /\ b``\ は、型チェックを通りません。これを修正するために、ブール式\ ``b``\ を形式的に「持ち上げ」て、表明にしなければなりません。このために\ ``bassn b``\ と書きます。これは"ブール式\ ``b``\ の評価結果が(任意の状態で)\ ``true``\ になる"という表明です。

::

    Definition bassn b : Assertion :=
      fun st => (beval st b = true).

``bassn``\ についての2つの便利な事実です:

::

    Lemma bexp_eval_true : forall b st,
      beval st b = true -> (bassn b) st.
    Proof.
      intros b st Hbe.
      unfold bassn. assumption.  Qed.

    Lemma bexp_eval_false : forall b st,
      beval st b = false -> ~ ((bassn b) st).
    Proof.
      intros b st Hbe contra.
      unfold bassn in contra.
      rewrite -> contra in Hbe. inversion Hbe.  Qed.

いよいよ条件分岐についてのホーア証明規則を形式化し、正しいことを証明できます。

::

    Theorem hoare_if : forall P Q b c1 c2,
      {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
      {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
      {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
    Proof.
      intros P Q b c1 c2 HTrue HFalse st st' HE HP.
      inversion HE; subst.
      Case "b is true".
        apply (HTrue st st').
          assumption.
          split. assumption.
                 apply bexp_eval_true. assumption.
      Case "b is false".
        apply (HFalse st st').
          assumption.
          split. assumption.
                 apply bexp_eval_false. assumption. Qed.

以下が、最初に挙げたプログラムが与えられた条件を満たすことの証明です。

::

    Example if_example :
        {{fun st => True}}
      IFB (BEq (AId X) (ANum 0))
        THEN (Y ::= (ANum 2))
        ELSE (Y ::= APlus (AId X) (ANum 1))
      FI
        {{fun st => asnat (st X) <= asnat (st Y)}}.
    Proof.

      apply hoare_if.
      Case "Then".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold bassn, assn_sub, update. simpl. intros.
        inversion H.
           symmetry in H1; apply beq_nat_eq in H1.
           rewrite H1.  omega.
      Case "Else".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assn_sub, update; simpl; intros. omega.
    Qed.

ループ
^^^^^^

最後に、ループについての推論規則が必要です。次のループを考えます:

::

          WHILE b DO c END

そして、次の三つ組が正しくなる事前条件\ ``P``\ と事後条件\ ``Q``\ を探します:

::

          {{P}} WHILE b DO c END {{Q}}

まず、\ ``b``\ が最初から偽であるときを考えましょう。このときループの本体はまったく実行されません。この場合は、ループは\ ``SKIP``\ と同様の振舞いをしますので、次のように書いても良いかもしれません。

::

          {{P}} WHILE b DO c END {{P}}.

しかし、条件分岐について議論したのと同様に、最後でわかっていることはもう少し多いのです。最終状態では\ ``P``\ であるだけではなく\ ``b``\ が偽になっているのです。そこで、事後条件にちょっと付け足すことができます:

::

          {{P}} WHILE b DO c END {{P /\ ~b}}

それでは、ループの本体が実行されるときはどうなるでしょう？ループを最後に抜けるときには\ ``P``\ が成立することを確実にするために、コマンド\ ``c``\ の終了時点で常に\ ``P``\ が成立することを確認する必要があるのは確かでしょう。さらに、\ ``P``\ が\ ``c``\ の最初の実行の前に成立しており、\ ``c``\ を実行するたびに、終了時点で\ ``P``\ の成立が再度確立されることから、\ ``P``\ が\ ``c``\ の実行前に常に成立していると仮定することができます。このことから次の規則が得られます:

::

                       {{P}} c {{P}}
            -----------------------------------
            {{P}} WHILE b DO c END {{P /\ ~b}}

命題\ ``P``\ は不変条件(*invariant*)と呼ばれます。

これで求める規則にかなり近付いたのですが、もうちょっとだけ改良できます。ループ本体の開始時点で、\ ``P``\ が成立しているだけでなく、ガード\ ``b``\ が現在の状態で真であるということも言えます。このことは、\ ``c``\ についての推論の際にいくらかの情報を与えてくれます。結局、規則の最終バージョンはこうなります:

::

                   {{P /\ b}} c {{P}}
            -----------------------------------  [hoare_while]
            {{P}} WHILE b DO c END {{P /\ ~b}}

    Lemma hoare_while : forall P b c,
      {{fun st => P st /\ bassn b st}} c {{P}} ->
      {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
    Proof.
      intros P b c Hhoare st st' He HP.


      remember (WHILE b DO c END) as wcom.
      ceval_cases (induction He) Case; try (inversion Heqwcom); subst.

      Case "E_WhileEnd".
        split. assumption. apply bexp_eval_false.  assumption.

      Case "E_WhileLoop".
        apply IHHe2.  reflexivity.
        apply (Hhoare st st'); try assumption.
          split. assumption. apply bexp_eval_true. assumption.  Qed.

    Example while_example :
        {{fun st => asnat (st X) <= 3}}
      WHILE (BLe (AId X) (ANum 2))
      DO X ::= APlus (AId X) (ANum 1) END
        {{fun st => asnat (st X) = 3}}.
    Proof.
      eapply hoare_consequence_post.
      apply hoare_while.
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      unfold bassn,  assn_sub. intros.  rewrite update_eq. simpl.
         inversion H as [_ H0].  simpl in H0. apply ble_nat_true in H0.
         omega.
      unfold bassn. intros. inversion H as [Hle Hb]. simpl in Hb.
         remember (ble_nat (asnat (st X)) 2) as le.  destruct le.
         apply ex_falso_quodlibet. apply Hb; reflexivity.
         symmetry in Heqle. apply ble_nat_false in Heqle. omega.
    Qed.

while規則を使うと、次のホーアの三つ組も証明できます。これは最初は驚くでしょう...

::

    Theorem always_loop_hoare : forall P Q,
      {{P}} WHILE BTrue DO SKIP END {{Q}}.
    Proof.
      intros P Q.
      apply hoare_consequence_pre with (P' := fun st : state => True).
      eapply hoare_consequence_post.
      apply hoare_while.
      Case "Loop body preserves invariant".
        apply hoare_post_true. intros st. apply I.
      Case "Loop invariant and negated guard imply postcondition".
        simpl. intros st [Hinv Hguard].
        apply ex_falso_quodlibet. apply Hguard. reflexivity.
      Case "Precondition implies invariant".
        intros st H. constructor.  Qed.

実際は、この結果は驚くことはないのです。ふり返って\ ``hoare_triple``\ の定義を見てみると、コマンドが停止した場合「のみ」に意味がある表明をしているのです。

::

    Print hoare_triple.

もしコマンドが停止しなければ、事後条件で何でも好きなことが証明できます。以下は、同じことのより直接的な証明です:

::

    Theorem always_loop_hoare' : forall P Q,
      {{P}} WHILE BTrue DO SKIP END {{Q}}.
    Proof.
      unfold hoare_triple. intros P Q st st' contra.
      apply loop_never_stops in contra.  inversion contra.
    Qed.

停止するコマンドについてだけを議論するホーア規則は、「部分」正当性("partial"
correctness)を記述していると言われます。「完全」正当性("total"
correctness)についてのホーア規則を与えることも可能です。それは、コマンドが停止するという事実を組み込んだものです。

練習問題:``REPEAT``\ のホーア規則
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

    Module RepeatExercise.

練習問題: ★★★★ (hoare\_repeat)
''''''''''''''''''''''''''''''

この練習問題では、コマンド言語に新たなコンストラクタ\ ``CRepeat``\ を追加します。\ ``repeat``\ の評価規則を記述し、このコマンドを含むプログラムについての新たなホーア論理の定理を、言語に追加しなさい。

以降の問題に進む前にこの練習問題をやっておくことをお勧めします。この問題は、素材の理解を確固としたものにする助けになるからです。

::

    Inductive com : Type :=
      | CSkip : com
      | CAss : id -> aexp -> com
      | CSeq : com -> com -> com
      | CIf : bexp -> com -> com -> com
      | CWhile : bexp -> com -> com
      | CRepeat : com -> bexp -> com.

``REPEAT``\ は\ ``WHILE``\ と同じように振舞います。ただし、ループのガードが本体の実行の「後で」評価され、それが「偽」である間はループがくりかえされるという点が違います。このことにより、本体は常に少なくとも1回は実行されることになります。

::

    Tactic Notation "com_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
      | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CRepeat" ].

    Notation "'SKIP'" :=
      CSkip.
    Notation "c1 ; c2" :=
      (CSeq c1 c2) (at level 80, right associativity).
    Notation "X '::=' a" :=
      (CAss X a) (at level 60).
    Notation "'WHILE' b 'DO' c 'END'" :=
      (CWhile b c) (at level 80, right associativity).
    Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
      (CIf e1 e2 e3) (at level 80, right associativity).
    Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
      (CRepeat e1 b2) (at level 80, right associativity).

以下の\ ``ceval``\ に\ ``REPEAT``\ の新たな規則を追加しなさい。\ ``WHILE``\ の規則を参考にして構いません。ただ、\ ``REPEAT``\ の本体は1度は実行されることと、ループの終了はガードが真になったときであることは忘れないで下さい。そして、この場合を扱えるように、\ ``ceval_cases``\ タクティックを更新しなさい。

::

    Inductive ceval : state -> com -> state -> Prop :=
      | E_Skip : forall st,
          ceval st SKIP st
      | E_Ass  : forall st a1 n V,
          aeval st a1 = n ->
          ceval st (V ::= a1) (update st V n)
      | E_Seq : forall c1 c2 st st' st'',
          ceval st c1 st' ->
          ceval st' c2 st'' ->
          ceval st (c1 ; c2) st''
      | E_IfTrue : forall st st' b1 c1 c2,
          beval st b1 = true ->
          ceval st c1 st' ->
          ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
      | E_IfFalse : forall st st' b1 c1 c2,
          beval st b1 = false ->
          ceval st c2 st' ->
          ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
      | E_WhileEnd : forall b1 st c1,
          beval st b1 = false ->
          ceval st (WHILE b1 DO c1 END) st
      | E_WhileLoop : forall st st' st'' b1 c1,
          beval st b1 = true ->
          ceval st c1 st' ->
          ceval st' (WHILE b1 DO c1 END) st'' ->
          ceval st (WHILE b1 DO c1 END) st''
    (* FILL IN HERE *)
    .

    Tactic Notation "ceval_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
      | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
      | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
    (* FILL IN HERE *)
    ].

上記から2つの定義のコピーし、新しい\ ``ceval``\ を使うようにしました。

::

    Notation "c1 '/' st '||' st'" := (ceval st c1 st')
                                     (at level 40, st at level 39).
    Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                            : Prop :=
      forall st st', (c / st || st') -> P st -> Q st'.
    Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

``repeat``\ コマンドの適切な証明規則を表現する定理\ ``hoare_repeat``\ を述べ、証明しなさい。このときに\ ``hoare_while``\ をモデルとして利用しなさい。

::

    (* FILL IN HERE *)

    End RepeatExercise.

☐

修飾付きプログラム
~~~~~~~~~~~~~~~~~~

ホーア論理の一番のポイントは、合成的ということです。証明の構造は常にプログラムの構造に従います。このことから、それぞれの文の周辺を適切な表明で修飾することで(低レベルの計算の詳細を省いた)証明の本質的アイデアを非形式的に記録できるのではないか、と考えられます。そういった修飾付きプログラム(*decorated
program*)は、自身の正しさの(非形式的)証明を伴っています。

例えば、次は完全な修飾付きプログラムです:

::

          {{ True }} =>
          {{ x = x }}
        X ::= x;
          {{ X = x }} =>
          {{ X = x /\ z = z }}
        Z ::= z;
          {{ X = x /\ Z = z }} =>
          {{ Z - X = z - x }}
        WHILE X <> 0 DO
            {{ Z - X = z - x /\ X <> 0 }} =>
            {{ (Z - 1) - (X - 1) = z - x }}
          Z ::= Z - 1;
            {{ Z - (X - 1) = z - x }}
          X ::= X - 1
            {{ Z - X = z - x }}
        END;
          {{ Z - X = z - x /\ ~ (X <> 0) }} =>
          {{ Z = z - x }} =>
          {{ Z + 1 = z - x + 1 }}
        Z ::= Z + 1
          {{ Z = z - x + 1 }}

具体的には、修飾付きプログラムはプログラムテキストと表明が交互に記述されたものです。修飾付きプログラムが正しい証明を表現していることをチェックするには、個々のコマンドが前後の表明と整合していることを「ローカルに」チェックします。このローカルな整合性チェックは次のようになります:

-  ``SKIP``\ は事前条件と事後条件が同じときに、整合しています。

   ::

             {{ P }}
             SKIP
             {{ P }}

-  ``c1``\ と\ ``c2``\ のコマンド合成が(表明\ ``P``\ と\ ``R``\ に関して)ローカルに整合的であるとは、\ ``c1``\ が(``P``\ と\ ``Q``\ に関して)整合的であり、\ ``c2``\ が(``Q``\ と\ ``R``\ に関して)整合的であることです:

   ::

             {{ P }}
             c1;
             {{ Q }}
             c2
             {{ R }}

-  代入がローカルに整合的であるとは、事後条件を適切に置換したものが事前条件であることです:

   ::

             {{ P where a is substituted for X }}
             X ::= a
             {{ P }}

-  条件分岐が(表明\ ``P``\ と\ ``Q``\ に関して)ローカルに整合的であるとは、
   "then"と"else"の枝の最初の表明がそれぞれ\ ``P/\b``\ と\ ``P/\~b``\ であり、"then"枝が(``P/\b``\ と\ ``Q``\ に関して)ローカルに整合的で、"else"枝が(``P/\~b``\ と\ ``Q``\ に関して)ローカルに整合的であることです:

   ::

             {{ P }}
             IFB b THEN
               {{ P /\ b }}
               c1
               {{ Q }}
             ELSE
               {{ P /\ ~b }}
               c2
               {{ Q }}
             FI

-  While
   ループがローカルに整合的であるとは、(事前条件を\ ``P``\ とするとき)
   事後条件が\ ``P/\~b``\ であって、ループ本体の事前条件と事後条件がそれぞれ\ ``P/\b``\ と\ ``P``\ であることです:

   ::

             {{ P }}
             WHILE b DO
               {{ P /\ b }}
               c1
               {{ P }}
             END
             {{ P /\ ~b }}

-  ``=>``\ の前後に1つずつの表明が並べられたものがローカルに整合的であるとは、\ ``=>``\ の前の表明が成立するならば\ ``=>``\ の後の表明が成立するということが(すべての状態で)言えることです:

   ::

             {{ P }} =>
             {{ P' }}

ホーア論理によるプログラムについての推論
----------------------------------------

例: 遅い引き算
~~~~~~~~~~~~~~

非形式的には:

::

          {{ X = x /\ Z = z }} =>
          {{ Z - X = z - x }}
        WHILE X <> 0 DO
            {{ Z - X = z - x /\ X <> 0 }} =>
            {{ (Z - 1) - (X - 1) = z - x }}
          Z ::= Z - 1;
            {{ Z - (X - 1) = z - x }}
          X ::= X - 1
            {{ Z - X = z - x }}
        END
          {{ Z - X = z - x /\ ~ (X <> 0) }} =>
          {{ Z = z - x }}

形式的には:

::

    Definition subtract_slowly : com :=
      WHILE BNot (BEq (AId X) (ANum 0)) DO
        Z ::= AMinus (AId Z) (ANum 1);
        X ::= AMinus (AId X) (ANum 1)
      END.

    Definition subtract_slowly_invariant x z :=
      fun st => minus (asnat (st Z)) (asnat (st X)) = minus z x.

    Theorem subtract_slowly_correct : forall x z,
      {{fun st => asnat (st X) = x /\ asnat (st Z) = z}}
      subtract_slowly
      {{fun st => asnat (st Z) = minus z x}}.
    Proof.



      intros x z. unfold subtract_slowly.


      eapply hoare_consequence with (P' := subtract_slowly_invariant x z).
      apply hoare_while.

      Case "Loop body preserves invariant".


        eapply hoare_seq. apply hoare_asgn.


        eapply hoare_consequence_pre. apply hoare_asgn.


        unfold subtract_slowly_invariant, assn_sub, update, bassn. simpl.
        intros st [Inv GuardTrue].


        remember (beq_nat (asnat (st X)) 0) as Q; destruct Q.
         inversion GuardTrue.
         symmetry in HeqQ.  apply beq_nat_false in HeqQ.
         omega. 
      Case "Initial state satisfies invariant".


        unfold subtract_slowly_invariant.
        intros st [HX HZ]. omega.
      Case "Invariant and negated guard imply postcondition".


        intros st [Inv GuardFalse].
        unfold subtract_slowly_invariant in Inv.
        unfold bassn in GuardFalse. simpl in GuardFalse.


        destruct (asnat (st X)).
          omega.
          apply ex_falso_quodlibet.   apply GuardFalse. reflexivity.
        Qed.

練習問題: ゼロへの簡約
~~~~~~~~~~~~~~~~~~~~~~

次の while ループは、非常にシンプルなため、不変条件が必要ありません:

::

              {{ True }}
            WHILE X <> 0 DO
                {{ True /\ X <> 0 }} =>
                {{ True }}
              X ::= X - 1
                {{ True }}
            END
              {{ True /\ X = 0 }} =>
              {{ X = 0 }}

この証明を Coq
に変換しなさい。\ ``slow_subtraction``\ の証明がアイデアの参考になるでしょう。

練習問題: ★★ (reduce\_to\_zero\_correct)
''''''''''''''''''''''''''''''''''''''''

::

    Definition reduce_to_zero : com :=
      WHILE BNot (BEq (AId X) (ANum 0)) DO
        X ::= AMinus (AId X) (ANum 1)
      END.

    Theorem reduce_to_zero_correct :
      {{fun st => True}}
      reduce_to_zero
      {{fun st => asnat (st X) = 0}}.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: 遅い足し算
~~~~~~~~~~~~~~~~~~~~

次のプログラムは変数Xを変数Zに足します。そのために、Xを減らしてZを増やすということを繰り返します。

::

    Definition add_slowly : com :=
      WHILE BNot (BEq (AId X) (ANum 0)) DO
        Z ::= APlus (AId Z) (ANum 1);
        X ::= AMinus (AId X) (ANum 1)
      END.

練習問題: ★★★ (add\_slowly\_decoration)
'''''''''''''''''''''''''''''''''''''''

上記の例\ ``subtract_slowly``\ のパターンに従って、\ ``add_slowly``\ の適切な事前条件と事後条件を与えなさい。次に(非形式的に)そのプログラムを前例にならって修飾しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: ★★★ (add\_slowly\_formal)
'''''''''''''''''''''''''''''''''''

Coq
の\ ``Hoare_triple``\ のように、\ ``add_slowly``\ の仕様を形式的に記述しなさい。そして正しさを証明しなさい。

::

    (* FILL IN HERE *)

☐

例: パリティ
~~~~~~~~~~~~

次は、よりトリッキーな例です。修飾付きプログラムを完全に理解していることを確認してください。Coqの証明の詳細のすべてを理解することが必要なわけではありません(それは、それほど大変ではないですが)。すべての必要なアイデアは非形式的なバージョンの中に含まれています。

::

        {{ X = x }} =>
        {{ X = x /\ 0 = 0 }}
      Y ::= 0;
        {{ X = x /\ Y = 0 }} =>
        {{ (Y=0 <-> ev (x-X)) /\ X<=x }}
      WHILE X <> 0 DO
          {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
          {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }}
        Y ::= 1 - Y;
          {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
        X ::= X - 1
          {{ Y=0 <-> ev (x-X) /\ X<=x }}
      END
        {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} =>
        {{ Y=0 <-> ev x }}

    Definition find_parity : com :=
      Y ::= (ANum 0);
      WHILE (BNot (BEq (AId X) (ANum 0))) DO
        Y ::= AMinus (ANum 1) (AId Y);
        X ::= AMinus (AId X) (ANum 1)
      END.

    Definition find_parity_invariant x :=
      fun st =>
           asnat (st X) <= x
        /\ (asnat (st Y) = 0 /\ ev (x - asnat (st X)) \/ asnat (st Y) = 1 /\ ~ev (x - asnat (st X))).



    Lemma not_ev_ev_S_gen: forall n,
      (~ ev n -> ev (S n)) /\
      (~ ev (S n) -> ev (S (S n))).
    Proof.
      induction n as [| n'].
      Case "n = 0".
        split; intros H.
        SCase "->".
          apply ex_falso_quodlibet. apply H. apply ev_0.
        SCase "<-".
          apply ev_SS. apply ev_0.
      Case "n = S n'".
        inversion IHn' as [Hn HSn]. split; intros H.
        SCase "->".
          apply HSn. apply H.
        SCase "<-".
          apply ev_SS. apply Hn. intros contra.
          apply H. apply ev_SS. apply contra.  Qed.

    Lemma not_ev_ev_S : forall n,
      ~ ev n -> ev (S n).
    Proof.
      intros n.
      destruct (not_ev_ev_S_gen n) as [H _].
      apply H.
    Qed.

    Theorem find_parity_correct : forall x,
      {{fun st => asnat (st X) = x}}
      find_parity
      {{fun st => asnat (st Y) = 0 <-> ev x}}.
    Proof.
      intros x. unfold find_parity.
      apply hoare_seq with (Q := find_parity_invariant x).
      eapply hoare_consequence.
      apply hoare_while with (P := find_parity_invariant x).
      Case "Loop body preserves invariant".
        eapply hoare_seq.
        apply hoare_asgn.
        eapply hoare_consequence_pre.
        apply hoare_asgn.
        intros st [[Inv1 Inv2] GuardTrue].
        unfold find_parity_invariant, bassn, assn_sub, aeval in *.
        rewrite update_eq.
        rewrite (update_neq Y X); auto.
        rewrite (update_neq X Y); auto.
        rewrite update_eq.
        simpl in GuardTrue. destruct (asnat (st X)).
          inversion GuardTrue. simpl.
        split. omega.
        inversion Inv2 as [[H1 H2] | [H1 H2]]; rewrite H1;
                         [right|left]; (split; simpl; [omega |]).
        apply ev_not_ev_S in H2.
        replace (S (x - S n)) with (x-n) in H2 by omega.
        rewrite <- minus_n_O. assumption.
        apply not_ev_ev_S in H2.
        replace (S (x - S n)) with (x - n) in H2 by omega.
        rewrite <- minus_n_O. assumption.
      Case "Precondition implies invariant".
        intros st H. assumption.
      Case "Invariant implies postcondition".
        unfold bassn, find_parity_invariant. simpl.
        intros st [[Inv1 Inv2] GuardFalse].
        destruct (asnat (st X)).
          split; intro.
            inversion Inv2.
               inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega.
               assumption.
               inversion H0 as [H0' _]. rewrite H in H0'. inversion H0'.
            inversion Inv2.
               inversion H0. assumption.
               inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega.
               apply ex_falso_quodlibet. apply H1. assumption.
          apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
      Case "invariant established before loop".
        eapply hoare_consequence_pre.
        apply hoare_asgn.
        intros st H.
        unfold assn_sub, find_parity_invariant, update. simpl.
        subst.
        split.
        omega.
        replace (asnat (st X) - asnat (st X)) with 0 by omega.
        left. split. reflexivity.
        apply ev_0.  Qed.

練習問題: ★★★ (wrong\_find\_parity\_invariant)
''''''''''''''''''''''''''''''''''''''''''''''

``find_parity``\ の不変条件の主張として次のものはもっともらしく見えます。

::

    Definition find_parity_invariant' x :=
      fun st =>
        (asnat (st Y)) = 0 <-> ev (x - asnat (st X)).

これがなぜうまくはたらかないかを説明しなさい。(ヒント:
形式的証明を考え、その問題を探そうとするのは時間の無駄です。ループの本体が実際に性質を保存するかどうかだけを考えなさい。)

::

    (* FILL IN HERE *)

☐

例: 平方根の探索
~~~~~~~~~~~~~~~~

::

    Definition sqrt_loop : com :=
      WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                       (APlus (ANum 1) (AId Z)))
                (AId X) DO
        Z ::= APlus (ANum 1) (AId Z)
      END.

    Definition sqrt_com : com :=
      Z ::= ANum 0;
      sqrt_loop.

    Definition sqrt_spec (x : nat) : Assertion :=
      fun st =>
           ((asnat (st Z)) * (asnat (st Z))) <= x
        /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x).

    Definition sqrt_inv (x : nat) : Assertion :=
      fun st =>
           asnat (st X) = x
        /\ ((asnat (st Z)) * (asnat (st Z))) <= x.

    Theorem random_fact_1 : forall st,
         (S (asnat (st Z))) * (S (asnat (st Z))) <= asnat (st X) ->
         bassn (BLe (AMult (APlus (ANum 1) (AId Z))
                           (APlus (ANum 1) (AId Z)))
                    (AId X)) st.
    Proof.
      intros st Hle.  unfold bassn. simpl.
      destruct (asnat (st X)) as [|x'].
      Case "asnat (st X) = 0".
        inversion Hle.
      Case "asnat (st X) = S x'".
        simpl in Hle. apply le_S_n in Hle.
        remember (ble_nat (plus (asnat (st Z))
                          ((asnat (st Z)) * (S (asnat (st Z))))) x')
          as ble.
        destruct ble. reflexivity.
        symmetry in Heqble. apply ble_nat_false in Heqble.
        unfold not in Heqble. apply Heqble in Hle. inversion Hle.
    Qed.

    Theorem random_fact_2 : forall st,
         bassn (BLe (AMult (APlus (ANum 1) (AId Z))
                           (APlus (ANum 1) (AId Z)))
                    (AId X)) st ->
           asnat (aeval st (APlus (ANum 1) (AId Z)))
         * asnat (aeval st (APlus (ANum 1) (AId Z)))
         <= asnat (st X).
    Proof.
      intros st Hble. unfold bassn in Hble. simpl in *.
      destruct (asnat (st X)) as [| x'].
      Case "asnat (st X) = 0".
        inversion Hble.
      Case "asnat (st X) = S x'".
        apply ble_nat_true in Hble. omega. Qed.

    Theorem sqrt_com_correct : forall x,
      {{fun st => True}} (X ::= ANum x; sqrt_com) {{sqrt_spec x}}.
    Proof.
      intros x.
      apply hoare_seq with (Q := fun st => asnat (st X) = x).
      Case "sqrt_com".
        unfold sqrt_com.
        apply hoare_seq with (Q := fun st => asnat (st X) = x
                                          /\ asnat (st Z) = 0).

        SCase "sqrt_loop".
          unfold sqrt_loop.
          eapply hoare_consequence.
          apply hoare_while with (P := sqrt_inv x).

          SSCase "loop preserves invariant".
            eapply hoare_consequence_pre.
            apply hoare_asgn. intros st H.
            unfold assn_sub. unfold sqrt_inv in *.
            inversion H as [[HX HZ] HP]. split.
            SSSCase "X is preserved".
              rewrite update_neq; auto.
            SSSCase "Z is updated correctly".
              rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
              subst. apply random_fact_2. assumption.

          SSCase "invariant is true initially".
            intros st H. inversion H as [HX HZ].
            unfold sqrt_inv. split. assumption.
            rewrite HZ. simpl. omega.

          SSCase "after loop, spec is satisfied".
            intros st H. unfold sqrt_spec.
            inversion H as [HX HP].
            unfold sqrt_inv in HX.  inversion HX as [HX' Harith].
            split. assumption.
            intros contra. apply HP. clear HP.
            simpl. simpl in contra.
            apply random_fact_1. subst x. assumption.

        SCase "Z set to 0".
          eapply hoare_consequence_pre. apply hoare_asgn.
          intros st HX.
          unfold assn_sub. split.
          rewrite update_neq; auto.
          rewrite update_eq; auto.

      Case "assignment of X".
        eapply hoare_consequence_pre. apply hoare_asgn.
        intros st H.
        unfold assn_sub. rewrite update_eq; auto.  Qed.

練習問題: ★★★, optional (sqrt\_informal)
''''''''''''''''''''''''''''''''''''''''

上記の正しさの証明に対応する修飾付きプログラムを記述しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: 階乗
~~~~~~~~~~~~~~

::

    Module Factorial.

    Fixpoint real_fact (n:nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (real_fact n')
      end.

階乗を計算する Imp プログラムを思い出してください:

::

    Definition fact_body : com :=
      Y ::= AMult (AId Y) (AId Z);
      Z ::= AMinus (AId Z) (ANum 1).

    Definition fact_loop : com :=
      WHILE BNot (BEq (AId Z) (ANum 0)) DO
        fact_body
      END.

    Definition fact_com : com :=
      Z ::= (AId X);
      Y ::= ANum 1;
      fact_loop.

練習問題: ★★★, optional (fact\_informal)
''''''''''''''''''''''''''''''''''''''''

::

    [[
        {{ X = x }}
      Z ::= X;
      Y ::= 1;
      WHILE Z <> 0 DO
        Y ::= Y * Z;
        Z ::= Z - 1
      END
        {{ Y = real_fact x }}
    ]]
    *)

FILL IN HERE
``fact_com``\ を修飾して、以下の事前条件、事後条件として与えられる仕様を満たすことを示しなさい。帰結規則のために(形式的には)算術式や不等号などについての推論が必要になりますが、ここまでと同様、それらは省略して構いません。

(\* FILL IN HERE \*)

::

        {{ X = x }}
      Z ::= X;
      Y ::= 1;
      WHILE Z <> 0 DO
        Y ::= Y * Z;
        Z ::= Z - 1
      END
        {{ Y = real_fact x }}

☐

練習問題: ★★★★, optional (fact\_formal)
'''''''''''''''''''''''''''''''''''''''

fact\_com
がこの仕様を満たすことを、形式的に証明しなさい。その際、自分の非形式的な証明をガイドとして使いなさい。(例で行ったように)ループ不変条件を分離して主張しても構いません。

::

    Theorem fact_com_correct : forall x,
      {{fun st => asnat (st X) = x}} fact_com
      {{fun st => asnat (st Y) = real_fact x}}.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

::

    End Factorial.

リストを扱うプログラムについての推論
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

練習問題: ★★★ (list\_sum)
'''''''''''''''''''''''''

以下は、リストの要素の合計の直接的定義と、その合計を計算するImpプログラムです

::

    Definition sum l := fold_right plus 0 l.

    Definition sum_program :=
      Y ::= ANum 0;
      WHILE (BIsCons (AId X)) DO
        Y ::= APlus (AId Y) (AHead (AId X)) ;
        X ::= ATail (AId X)
      END.

``sum_program``\ の以下の仕様の「非形式的な」証明を、修飾を付けたバージョンのプログラムの形で与えなさい。

::

    Definition sum_program_spec := forall l,
      {{ fun st => aslist (st X) = l }}
      sum_program
      {{ fun st => asnat (st Y) = sum l }}.

    (* FILL IN HERE *)

☐ \*

次に、リストを扱うあるプログラムの「形式的な」ホーア論理の証明を見てみましょう。次のプログラムは、数値\ ``Y``\ がリスト\ ``X``\ の中に含まれるかどうかをチェックし、もし含まれたならば\ ``Z``\ を\ ``1``\ にします。このプログラムを検証します。

::

    Definition list_member :=
      WHILE BIsCons (AId X) DO
        IFB (BEq (AId Y) (AHead (AId X))) THEN
          Z ::= (ANum 1)
        ELSE
          SKIP
        FI;
        X ::= ATail (AId X)
      END.

    Definition list_member_spec := forall l n,
      {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
      list_member
      {{ fun st => st Z = VNat 1 <-> appears_in n l }}.

証明は非形式的に書くと次のようになるものを使います:

::

        {{ X = l /\ Y = n /\ Z = 0 }} =>
        {{ Y = n /\ exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p) }}
      WHILE (BIsCons X)
      DO
          {{ Y = n /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
                   /\ (BIsCons X) }}
        IFB (Y == head X) THEN
            {{ Y = n
               /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
               /\ (BIsCons X)
               /\ Y == AHead X }} =>
            {{ Y = n /\ (exists p, p ++ tail X = l
                        /\ (1 = 1 <-> appears_in n p)) }}
          Z ::= 1
            {{ Y = n /\ (exists p, p ++ tail X = l
            /\ (Z = 1 <-> appears_in n p)) }}
        ELSE
            {{ Y = n
               /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
               /\ (BIsCons X)
               /\ ~ (Y == head X) }} =>
            {{ Y = n
               /\ (exists p, p ++ tail X = l /\ (Z = 1 <-> appears_in n p)) }}
          SKIP
            {{ Y = n
               /\ (exists p, p ++ tail X = l /\ (Z = 1 <-> appears_in n p)) }}
        FI;
        X ::= ATail X
            {{ Y = n
               /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)) }}
      END
         {{ Y = n
            /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
            /\ ~ (BIsCons X) }} =>
         {{ Z = 1 <-> appears_in n l }}

証明で興味深い点はただ1つ、ループ不変条件の選び方です:

::

          exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)

これは、ループの繰り返しのたびに、もとのリスト\ ``l``\ が\ ``X``\ の現在値と別のリスト\ ``p``\ とを結合したものと同一であることを言っています。この\ ``p``\ はプログラム内の変数の値ではないですが、最初から証明が進んでいく間、保持されていきます。(このような\ ``p``\ は、よく"幽霊変数"(ghost
variable)と呼ばれます。)

このようなリスト\ ``p``\ が存在することを示すために、繰り返しの毎回、\ ``X``\ の先頭に\ ``p``\ の「最後」を加えています。このために
Poly\_J.vの\ ``snoc``\ を使っています。

::

    Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
      match l with
      | nil      =>  [ v ]
      | cons h t => h :: (snoc t v)
      end.

    Lemma snoc_equation : forall (A : Type) (h:A) (x y : list A),
      snoc x h ++ y = x ++ h :: y.
    Proof.
      intros A h x y.
      induction x.
        Case "x = []". reflexivity.
        Case "x = cons". simpl. rewrite IHx. reflexivity.
    Qed.

メインの証明はたくさんの補題を使います。

::

    Lemma appears_in_snoc1 : forall a l,
      appears_in a (snoc l a).
    Proof.
      induction l.
        Case "l = []". apply ai_here.
        Case "l = cons". simpl. apply ai_later. apply IHl.
    Qed.

    Lemma appears_in_snoc2 : forall a b l,
      appears_in a l ->
      appears_in a (snoc l b).
    Proof.
      induction l; intros H; inversion H; subst; simpl.
        Case "l = []". apply ai_here.
        Case "l = cons". apply ai_later. apply IHl. assumption.
    Qed.

    Lemma appears_in_snoc3 : forall a b l,
       appears_in a (snoc l b) ->
       (appears_in a l \/ a = b).
    Proof.
       induction l; intros H.
       Case "l = []". inversion H.
         SCase "ai_here". right. reflexivity.
         SCase "ai_later". left. assumption.
       Case "l = cons". inversion H; subst.
         SCase "ai_here". left. apply ai_here.
         SCase "ai_later". destruct (IHl H1).
           left. apply ai_later. assumption.
           right. assumption.
    Qed.

    Lemma append_singleton_equation : forall (x : nat) l l',
      (l ++ [x]) ++ l' = l ++ x :: l'.
    Proof.
      intros x l l'.
      induction l.
        reflexivity.
        simpl. rewrite IHl. reflexivity.
    Qed.

    Lemma append_nil : forall (A : Type) (l : list A),
      l ++ [] = l.
    Proof.
      induction l.
        reflexivity.
        simpl. rewrite IHl. reflexivity.
    Qed.

    Lemma beq_true__eq : forall n n',
      beq_nat n n' = true ->
      n = n'.
    Proof.
      induction n; destruct n'.
      Case "n = 0, n' = 0".     reflexivity.
      Case "n = 0, n' = S _".   simpl. intros H. inversion H.
      Case "n = S, n' = 0".     simpl. intros H. inversion H.
      Case "n = S, n' = S".     simpl. intros H.
                                rewrite (IHn n' H). reflexivity.
    Qed.

    Lemma beq_nat_refl : forall n,
      beq_nat n n = true.
    Proof.
      induction n.
        reflexivity.
        simpl. assumption.
    Qed.

    Theorem list_member_correct : forall l n,
      {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
      list_member
      {{ fun st => st Z = VNat 1 <-> appears_in n l }}.
    Proof.
      intros l n.
      eapply hoare_consequence.
      apply hoare_while with (P := fun st =>
         st Y = VNat n
         /\ exists p, p ++ aslist (st X) = l
                      /\ (st Z = VNat 1 <-> appears_in n p)).

        eapply hoare_seq.
        apply hoare_asgn.
        apply hoare_if.
        Case "If taken".
          eapply hoare_consequence_pre.
          apply hoare_asgn.
          intros st [[[H1 [p [H2 H3]]] H9] H10].
          unfold assn_sub. split.

            rewrite update_neq; try reflexivity.
            rewrite update_neq; try reflexivity.
            assumption.


            remember (aslist (st X)) as x.
            destruct x as [|h x'].
              unfold bassn in H9. unfold beval in H9. unfold aeval in H9.
              rewrite <- Heqx in H9. inversion H9.

              exists (snoc p h).
              rewrite update_eq.
              unfold aeval. rewrite update_neq; try reflexivity.
              rewrite <- Heqx.
              split.
                rewrite snoc_equation. assumption.

                rewrite update_neq; try reflexivity.
                rewrite update_eq.
                split.
                  simpl.
                  unfold bassn in H10. unfold beval in H10.
                  unfold aeval in H10. rewrite H1 in H10.
                  rewrite <- Heqx in H10. simpl in H10.
                  rewrite (beq_true__eq _ _ H10).
                  intros. apply appears_in_snoc1.

                  intros. reflexivity.
        Case "If not taken".
          eapply hoare_consequence_pre. apply hoare_skip.
          unfold assn_sub.
          intros st [[[H1 [p [H2 H3]]] H9] H10].
          split.

            rewrite update_neq; try reflexivity.
            assumption.


            remember (aslist (st X)) as x.
            destruct x as [|h x'].
              unfold bassn in H9. unfold beval in H9. unfold aeval in H9.
              rewrite <- Heqx in H9. inversion H9.

              exists (snoc p h).
              split.
                rewrite update_eq.
                unfold aeval. rewrite <- Heqx.
                rewrite snoc_equation. assumption.

                rewrite update_neq; try reflexivity.
                split.
                  intros. apply appears_in_snoc2. apply H3. assumption.

                  intros.  destruct (appears_in_snoc3 _ _ _ H).
                  SCase "later".
                    inversion H3 as [_ H3'].
                    apply H3'. assumption.
                  SCase "here (absurd)".
                    subst.
                    unfold bassn in H10. unfold beval in H10. unfold aeval in H10.
                    rewrite <- Heqx in H10. rewrite H1 in H10.
                    simpl in H10. rewrite beq_nat_refl in H10.
                    apply ex_falso_quodlibet. apply H10. reflexivity.

      intros st [H1 [H2 H3]].
      rewrite H1. rewrite H2. rewrite H3.
      split.
        reflexivity.
        exists []. split.
          reflexivity.
          split; intros H; inversion H.

      simpl.   intros st [[H1 [p [H2 H3]]] H5].

      unfold bassn in H5. unfold beval in H5. unfold aeval in H5.
      destruct (aslist (st X)) as [|h x'].
        rewrite append_nil in H2.
        rewrite <- H2.
        assumption.

        apply ex_falso_quodlibet. apply H5. reflexivity.
    Qed.

練習問題: ★★★★, optional (list\_reverse)
''''''''''''''''''''''''''''''''''''''''

Poly\_J.vの\ ``rev``\ を思い出してください。リストを逆順にするものです。

::

    Fixpoint rev {X:Type} (l:list X) : list X :=
      match l with
      | nil      => []
      | cons h t => snoc (rev t) h
      end.

リストを逆順にする Imp
プログラム\ ``list_reverse_program``\ を記述しなさい。次の仕様を満たすことを形式的に証明しなさい:

::

        forall l : list nat,
          {{ X =  l /\ Y = nil }}
          list_reverse_program
          {{ Y = rev l }}.

補題\ ``append_nil``\ と\ ``rev_equation``\ を使うのが良いでしょう。

::

    Lemma rev_equation : forall (A : Type) (h : A) (x y : list A),
      rev (h :: x) ++ y = rev x ++ h :: y.
    Proof.
      intros. simpl. apply snoc_equation.
    Qed.

    (* FILL IN HERE *)

☐

修飾付きプログラムの形式化
--------------------------

ホーアの三つ組を、非形式的な修飾付きプログラムで記述することは結局、コマンドに十分な表明を付加することで、三つ組の正しさをチェックすることを、ある表明が別のものより強いことを示す簡単な代数的計算に簡約化することになります。

この節では、この非形式的なスタイルを、実際は完全に形式的に表現できることを示します。

構文
~~~~

最初にしなければならないことは、表明を埋め込んだコマンド構文を形式化することです。この形のコマンドを修飾付きコマンド(*decorated
commands*)または\ ``dcom``\ と呼びます。

::

    Inductive dcom : Type :=
      | DCSkip :  Assertion -> dcom
      | DCSeq : dcom -> dcom -> dcom
      | DCAsgn : id -> aexp ->  Assertion -> dcom
      | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom -> dcom
      | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
      | DCPre : Assertion -> dcom -> dcom
      | DCPost : dcom -> Assertion -> dcom.

    Tactic Notation "dcom_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
      | Case_aux c "If" | Case_aux c "While"
      | Case_aux c "Pre" | Case_aux c "Post" ].

    Notation "'SKIP' {{ P }}"
          := (DCSkip P)
          (at level 10) : dcom_scope.
    Notation "l '::=' a {{ P }}"
          := (DCAsgn l a P)
          (at level 60, a at next level) : dcom_scope.
    Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
          := (DCWhile b Pbody d Ppost)
          (at level 80, right associativity) : dcom_scope.
    Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI'"
          := (DCIf b P d P' d')
          (at level 80, right associativity)  : dcom_scope.
    Notation "'=>' {{ P }} d"
          := (DCPre P d)
          (at level 90, right associativity)  : dcom_scope.
    Notation "{{ P }} d"
          := (DCPre P d)
          (at level 90)  : dcom_scope.
    Notation "d '=>' {{ P }}"
          := (DCPost d P)
          (at level 91, right associativity)  : dcom_scope.
    Notation " d ; d' "
          := (DCSeq d d')
          (at level 80, right associativity)  : dcom_scope.

    Delimit Scope dcom_scope with dcom.

既に定義されているコマンド\ ``com``\ の記法\ ``Notation``\ との衝突を避けるため、\ ``dcom_scope``\ という特別なスコープを導入します。そして、例を宣言\ ``% dcom``\ で包み、記法をこのスコープ内で解釈したいことを表します。

注意深い読者は、\ ``DCPre``\ コンストラクタに対して2つの記法を定義していることに気付くでしょう。\ ``=>``\ を使うものと使わないものです。\ ``=>``\ を使わないものは、プログラムの一番最初の事前条件を与える意図で用意したものです。

::

    Example dec_while : dcom := (
        {{ fun st => True }}
      WHILE (BNot (BEq (AId X) (ANum 0)))
      DO
           {{ fun st => ~(asnat (st X) = 0) }}
          X ::= (AMinus (AId X) (ANum 1))
           {{ fun _ => True }}
      END
        {{ fun st => asnat (st X) = 0 }}
    ) % dcom.

``dcom``\ から\ ``com``\ に変換するのは簡単です。アノテーションをすべて消せば良いのです。

::

    Fixpoint extract (d:dcom) : com :=
      match d with
      | DCSkip _          => SKIP
      | DCSeq d1 d2       => (extract d1 ; extract d2)
      | DCAsgn V a _      => V ::= a
      | DCIf b _ d1 _ d2  => IFB b THEN extract d1 ELSE extract d2 FI
      | DCWhile b _ d _   => WHILE b DO extract d END
      | DCPre _ d         => extract d
      | DCPost d _        => extract d
      end.

``dcom``\ の定義のどこに表明を置くかの選択は、ちょっと微妙です。一番簡単な方法は、すべての\ ``dcom``\ に事前条件と事後条件の表明を付けてしまうことかもしれません。しかしそうすると、同じアノテーションが繰替えされて、とてもうるさいプログラムになってしまうでしょう。例えば、\ ``SKIP;SKIP``\ は次のように表明が付加されることになります。

::

            {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},

それぞれの\ ``SKIP``\ の事前条件、事後条件と、さらにセミコロンの事前条件、事後条件として同じものが付加されています!

この代わりに、次の規則に従うことにします:

-  ``dcom``d``\ に対する事後条件は\ ``d``\ に埋め込む
-  事前条件はコンテキストから与えられるようにする。

言い換えると、この表現での不変条件は、\ ``dcom``d``\ と事前条件\ ``P``\ がホーアの三つ組\ ``{{P}} (extract d) {{post d}}``\ を決定するということです。ここで\ ``post``\ は次のように定義されます:

::

    Fixpoint post (d:dcom) : Assertion :=
      match d with
      | DCSkip P                => P
      | DCSeq d1 d2             => post d2
      | DCAsgn V a Q            => Q
      | DCIf  _ _ d1 _ d2       => post d1
      | DCWhile b Pbody c Ppost => Ppost
      | DCPre _ d               => post d
      | DCPost c Q              => Q
      end.

修飾付きプログラムから「最初の事前条件」を抽出する同様の関数が定義できます。

::

    Fixpoint pre (d:dcom) : Assertion :=
      match d with
      | DCSkip P                => fun st => True
      | DCSeq c1 c2             => pre c1
      | DCAsgn V a Q            => fun st => True
      | DCIf  _ _ t _ e         => fun st => True
      | DCWhile b Pbody c Ppost => fun st => True
      | DCPre P c               => P
      | DCPost c Q              => pre c
      end.

この関数は、最弱事前条件を計算する、というような洗練されたことは何もしません。単に、プログラムの一番最初から明示的に付加されたアノテーションを再帰的に探します。もし(代入だけのものや\ ``SKIP``\ のように)明示的事前条件を持たない場合には、デフォルトの答えを返します。

``pre``\ と\ ``post``\ を使い、修飾付きプログラムの一番最初には常に明示的な事前条件のアノテーションを付ける慣習を守ることを仮定すると、修飾付きプログラムが正しいとはどういうことかを以下のように表現できます:

::

    Definition dec_correct (d:dcom) :=
      {{pre d}} (extract d) {{post d}}.

このホーアの三つ組が正しい(*valid*)かどうかをチェックするには、修飾付きプログラムから「証明課題」("proof
obligations")を抽出することが必要となります。この課題は、しばしば検証条件(*verification
conditions*)と呼ばれます。なぜなら、修飾が論理的に整合していて、全体として正しさの証明になることを確認するために(修飾付きプログラムを調べるプロセスによって)検証されるべき事実だからです。

検証条件の抽出
~~~~~~~~~~~~~~

最初に、記法について少々:

::

    Definition assert_implies (P Q : Assertion) : Prop :=
      forall st, P st -> Q st.

``assert_implies P Q``\ を\ ``P ~~> Q``\ (ASCIIでは,\ ``P ~``~> Q``)と書きます。

::

    Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
    Notation "P <~~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

次に、主要な定義です。関数\ ``verification_conditions``\ は\ ``dcom``d``\ と事前条件\ ``P``\ をとり、命題(*proposition*)を返します。その命題は、もし証明できたならば、三つ組\ ``{{P}} (extract d) {{post d}}``\ が正しいことになります。この関数はその命題を作るために、\ ``d``\ を調べまわって、すべてのローカルチェックの
/ (and)をとります。ローカルチェックとは、前に修飾付きプログラムについての非形式的規則のところでリストアップしたもののことです。(厳密に言うと、帰結規則の使用法を拡げるために非形式的規則をちょっと揉んでやる必要があります。ただ、対応関係は明確でしょう。)

::

    Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
      match d with
      | DCSkip Q          =>
          (P ~~> Q)
      | DCSeq d1 d2      =>
          verification_conditions P d1
          /\ verification_conditions (post d1) d2
      | DCAsgn V a Q      =>
          (P ~~> assn_sub V a Q)
      | DCIf b P1 t P2 e  =>
          ((fun st => P st /\ bassn b st) ~~> P1)
          /\ ((fun st => P st /\ ~ (bassn b st)) ~~> P2)
          /\ (post t = post e)
          /\ verification_conditions P1 t
          /\ verification_conditions P2 e
      | DCWhile b Pbody d Ppost      =>

          (P ~~> post d)
          /\ ((fun st => post d st /\ bassn b st) <~~> Pbody)
          /\ ((fun st => post d st /\ ~(bassn b st)) <~~> Ppost)
          /\ verification_conditions (fun st => post d st /\ bassn b st) d
      | DCPre P' d         =>
          (P ~~> P') /\ verification_conditions P' d
      | DCPost d Q        =>
          verification_conditions P d /\ (post d ~~> Q)
      end.

そしてついに、主定理です。この定理は、\ ``verification_conditions``\ 関数が正しくはたらくことを主張します。当然ながら、その証明にはホーア論理のすべての規則が必要となります。

これまで、いろいろなタクティックについて、ゴールではなくコンテキストの値に適用する別形を使ってきました。このアイデアの拡張が構文\ ``tactic in *``\ です。この構文では、\ ``tactic``\ をゴールとコンテキストのすべての仮定とに適用します。このしくみは、下記のように\ ``simpl``\ タクティックと組み合わせて使うのが普通です。

::

    Theorem verification_correct : forall d P,
      verification_conditions P d -> {{P}} (extract d) {{post d}}.
    Proof.
      dcom_cases (induction d) Case; intros P H; simpl in *.
      Case "Skip".
        eapply hoare_consequence_pre.
          apply hoare_skip.
          assumption.
      Case "Seq".
        inversion H as [H1 H2]. clear H.
        eapply hoare_seq.
          apply IHd2. apply H2.
          apply IHd1. apply H1.
      Case "Asgn".
        eapply hoare_consequence_pre.
          apply hoare_asgn.
          assumption.
      Case "If".
        inversion H as [HPre1 [HPre2 [HQeq [HThen HElse]]]]; clear H.
        apply hoare_if.
          eapply hoare_consequence_pre. apply IHd1. apply HThen. assumption.
          simpl. rewrite HQeq.
          eapply hoare_consequence_pre. apply IHd2. apply HElse. assumption.
      Case "While".
        rename a into Pbody. rename a0 into Ppost.
        inversion H as [Hpre [Hbody [Hpost Hd]]]; clear H.
        eapply hoare_consequence.
        apply hoare_while with (P := post d).
          apply IHd. apply Hd.
          assumption. apply Hpost.
      Case "Pre".
        inversion H as [HP Hd]; clear H.
        eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
      Case "Post".
        inversion H as [Hd HQ]; clear H.
        eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
    Qed.

例
~~

``verification_conditions``\ が生成する命題はかなり大きく、/ でつながれた命題の中には本質的に自明なものも多く含まれます。

::

    Eval simpl in (verification_conditions (fun st => True) dec_while).

ここまで見てきたタクティックだけを使うことでこれらの命題の証明を進めることは確かにできるのですが、いくらか自動化を入れることで、よりスムーズに進められるようにできます。最初に自前のタクティック\ ``verify``\ を定義します。このタクティックは、split
を繰り返し適用して/、その後\ ``omega``\ と\ ``eauto``\ (便利な一般用途のタクティック。後に詳しく議論します)を適用可能な限り使います。

::

    Tactic Notation "verify" :=
      try apply verification_correct;
      repeat split;
      simpl; unfold assert_implies;
      unfold bassn in *; unfold beval in *; unfold aeval in *;
      unfold assn_sub; simpl in *;
      intros;
      repeat match goal with [H : _ /\ _ |- _] => destruct H end;
      try eauto; try omega.

``verify``\ 適用後残るのは、修飾の正しさをチェックするのに「興味深い部分だけ」です。例えば:

::

    Theorem dec_while_correct :
      dec_correct dec_while.
    Proof.
      verify; destruct (asnat (st X)).
        inversion H0.
        unfold not. intros. inversion H1.
        apply ex_falso_quodlibet. apply H. reflexivity.
        reflexivity.
        reflexivity.
        apply ex_falso_quodlibet. apply H0. reflexivity.
        unfold not. intros. inversion H0.
        inversion H.
    Qed.

別の例(前に見た修飾付きプログラムを形式化したもの)です:

::

    Example subtract_slowly_dec (x:nat) (z:nat) : dcom := (
        {{ fun st => asnat (st X) = x /\ asnat (st Z) = z }}
      WHILE BNot (BEq (AId X) (ANum 0))
      DO   {{ fun st => asnat (st Z) - asnat (st X) = z - x
                     /\ bassn (BNot (BEq (AId X) (ANum 0))) st }}
         Z ::= AMinus (AId Z) (ANum 1)
           {{ fun st => asnat (st Z) - (asnat (st X) - 1) = z - x }} ;
         X ::= AMinus (AId X) (ANum 1)
           {{ fun st => asnat (st Z) - asnat (st X) = z - x }}
      END
        {{ fun st =>   asnat (st Z)
                     - asnat (st X)
                     = z - x
                  /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st }}
        =>
        {{ fun st => asnat (st Z) = z - x }}
    ) % dcom.

    Theorem subtract_slowly_dec_correct : forall x z,
      dec_correct (subtract_slowly_dec x z).
    Proof.
      intros. verify.
        rewrite <- H.
        assert (H1: update st Z (VNat (asnat (st Z) - 1)) X = st X).
          apply update_neq. reflexivity.
        rewrite -> H1. destruct (asnat (st X)) as [| X'].
          inversion H0. simpl. rewrite <- minus_n_O. omega.
        destruct (asnat (st X)).
          omega.
          apply ex_falso_quodlibet. apply H0. reflexivity.
    Qed.

練習問題: ★★★ (slow\_assignment\_dec)
'''''''''''''''''''''''''''''''''''''

``X``\ に現在設定されている値を変数\ ``Y``\ に代入する遠回りの方法は、\ ``Y``\ を\ ``0``\ から始め、\ ``X``\ を\ ``0``\ になるまで減らしていきながら、その各ステップで\ ``Y``\ を増やしていくことです。

次が、このアイデアを\ ``x``\ をパラメータとする非形式的な修飾付きプログラムで表したものです:

::

          {{ True }}
        X ::= x
          {{ X = x }} ;
        Y ::= 0
          {{ X = x /\ Y = 0 }} ;
        WHILE X <> 0 DO
            {{ X + Y = x /\ X > 0 }}
          X ::= X - 1
            {{ Y + X + 1 = x }} ;
          Y ::= Y + 1
            {{ Y + X = x }}
        END
          {{ Y = x /\ X = 0 }}

対応する\ ``dcom``\ 型の値を返す関数を記述し、その正しさを証明しなさい。

::

    (* FILL IN HERE *)

☐

練習問題: ★★★★, optional (factorial\_dec)
'''''''''''''''''''''''''''''''''''''''''

以前に扱った階乗関数を思い出してください:

::

    Fixpoint real_fact (n:nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (real_fact n')
      end.

``subtract_slowly_dec``\ のパターンに倣って、階乗計算の修飾付きImpプログラムを記述し、その正しさを証明しなさい。

::

    (* FILL IN HERE *)

☐

最後に、より大きな例として、新しい道具立てを使って\ ``list_member_correct``\ の証明を再度行ってみましょう。

``verify``\ タクティックは\ ``hoare_consequence``\ を利用するたびに(つまり修飾付きプログラムに\ ``=>``\ が現れるたびに)サブゴールを作ることに注意します。これらの含意は、リストについての事実(例えば\ ``l ++ [``\ =
l]など)に依存しています。言い換えると、ホーア論理のインフラは命令型プログラムの実行についての一般的な部分を扱い、一方ユーザは(例えば数値のリストという)問題領域特有の補題を証明しなければなりません。

::

    Definition list_member_dec (n : nat) (l : list nat) : dcom := (
        {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
      WHILE BIsCons (AId X)
      DO {{ fun st => st Y = VNat n
                   /\ (exists p, p ++ aslist (st X) = l
                   /\ (st Z = VNat 1 <-> appears_in n p))
                   /\ bassn (BIsCons (AId X)) st }}
        IFB (BEq (AId Y) (AHead (AId X))) THEN
            {{ fun st =>
              ((st Y = VNat n
                /\ (exists p, p ++ aslist (st X) = l
                    /\ (st Z = VNat 1 <-> appears_in n p)))
              /\ bassn (BIsCons (AId X)) st)
              /\ bassn (BEq (AId Y) (AHead (AId X))) st }}
            =>
            {{ fun st =>
                st Y = VNat n
                /\ (exists p, p ++ tail (aslist (st X)) = l
                     /\ (VNat 1 = VNat 1 <-> appears_in n p)) }}
          Z ::= ANum 1
            {{ fun st => st Y = VNat n
                 /\ (exists p, p ++ tail (aslist (st X)) = l
                      /\ (st Z = VNat 1 <-> appears_in n p)) }}
       ELSE
            {{ fun st =>
              ((st Y = VNat n
                /\ (exists p, p ++ aslist (st X) = l
                      /\ (st Z = VNat 1 <-> appears_in n p)))
              /\ bassn (BIsCons (AId X)) st)
              /\ ~bassn (BEq (AId Y) (AHead (AId X))) st }}
            =>
            {{ fun st =>
              st Y = VNat n
              /\ (exists p, p ++ tail (aslist (st X)) = l
                   /\ (st Z = VNat 1 <-> appears_in n p)) }}
          SKIP
            {{ fun st => st Y = VNat n
                /\ (exists p, p ++ tail (aslist (st X)) = l
                     /\ (st Z = VNat 1 <-> appears_in n p)) }}
       FI ;
       X ::= (ATail (AId X))
         {{ fun st  =>
             st Y = VNat n /\
             (exists p : list nat, p ++ aslist (st X) = l
               /\ (st Z = VNat 1 <-> appears_in n p)) }}
      END
       {{ fun st =>
         (st Y = VNat n
           /\ (exists p, p ++ aslist (st X) = l
                /\ (st Z = VNat 1 <-> appears_in n p)))
         /\ ~bassn (BIsCons (AId X)) st }}
       =>
       {{ fun st => st Z = VNat 1 <-> appears_in n l }}
    ) %dcom.

    Theorem list_member_correct' : forall n l,
      dec_correct (list_member_dec n l).
    Proof.
      intros n l.
      verify.
      Case "The loop precondition holds.".
        exists []. simpl. split.
          rewrite H. reflexivity.
          rewrite H1. split; inversion 1.
      Case "IF taken".
        destruct H2 as  [p [H3 H4]].

        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          inversion H1.
          exists (snoc p h).
          simpl. split.
             rewrite snoc_equation. assumption.
             split.
               rewrite H in H0.
               simpl in H0.
               rewrite (beq_true__eq _ _ H0).
               intros. apply appears_in_snoc1.
               intros. reflexivity.
      Case "If not taken".
        destruct H2 as [p [H3 H4]].

        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          inversion H1.
          exists (snoc p h).
          split.
            rewrite snoc_equation. assumption.
            split.
              intros. apply appears_in_snoc2. apply H4. assumption.
              intros Hai.  destruct (appears_in_snoc3 _ _ _ Hai).
              SCase "later". apply H4. assumption.
              SCase "here (absurd)".
                subst.
                simpl in H0. rewrite H in H0. rewrite beq_nat_refl in H0.
                apply ex_falso_quodlibet. apply H0. reflexivity.
      Case "Loop postcondition implies desired conclusion (->)".
        destruct H2 as [p [H3 H4]].
        unfold bassn in H1. simpl in H1.
        destruct (aslist (st X)) as [|h x'].
           rewrite append_nil in H3. subst. apply H4. assumption.
           apply ex_falso_quodlibet. apply H1. reflexivity.
      Case "loop postcondition implies desired conclusion (<-)".
        destruct H2 as [p [H3 H4]].
        unfold bassn in H1. simpl in H1.
        destruct (aslist (st X)) as [|h x'].
           rewrite append_nil in H3. subst. apply H4. assumption.
           apply ex_falso_quodlibet. apply H1. reflexivity.
    Qed.

