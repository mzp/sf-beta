MoreStlc\_J: 単純型付きラムダ計算についてさらに
===============================================

::

    Require Export Stlc_J.
    Require Import Relations.

STLCの単純な拡張
----------------

単純型付きラムダ計算は理論的性質を興味深いものにするには十分な構造を持っていますが、まだプログラミング言語といえるようなものではありません。この章では、型レベルでの直接的な扱いがあるいくつもの馴染み深い機能を導入することで、実世界の言語とのギャップを埋め始めます。

数値
^^^^

数値に関する型、定数、基本操作を追加することは容易です。\ ``Stlc_J``\ 章の前半と後半をくっつけるだけです。

``let``\ 束縛
^^^^^^^^^^^^^

複雑な式を書くとき、部分式に名前をつけるのが便利なことがよくあります。同じことを繰り返すのを避けることができ、またしばしば可読性が向上します。ほとんどの言語はこのための1つ以上の方法を持っています。OCaml(および
Coq)では、例えば\ ``let x=t1 in t2``\ と書くと「式\ ``t1``\ を評価して、その結果を名前\ ``x``\ に束縛して\ ``t2``\ を評価する」ことを意味します。

ここで導入する\ ``let``\ 束縛子はOCamlに従って値呼び(call-by-value)評価順序とします。つまり、\ ``let``\ 本体の評価が始まる前に\ ``let``\ 束縛項は完全に評価されます。型付け規則\ ``T_Let``\ は、\ ``let``\ の型が次の手順で計算されることを示しています:まず\ ``let``\ 束縛項の型の計算、次にその型の束縛によるコンテキストの拡張、さらにこの拡張されたコンテキストでの\ ``let``\ 本体の型の計算をすると、それが\ ``let``\ 式全体の型になります。

コースのこの時点では、新しい機能の定義のためにたくさんの日本語の文章を読み通すより、同じ情報を伝える規則を単に見る方が、おそらく簡単でしょう。以下がその規則です:

構文:

::

           t ::=                項
               | ...               (前と同じ他の項)
               | let x=t in t      let束縛

簡約:

::

                                     t1 ==> t1'
                         ----------------------------------               (ST_Let1)
                         let x=t1 in t2 ==> let x=t1' in t2

                            ----------------------------              (ST_LetValue)
                            let x=v1 in t2 ==> [v1/x] t2

型付け:

::

                    Gamma |- t1 : T1      Gamma , x:T1 |- t2 : T2
                    --------------------------------------------            (T_Let)
                            Gamma |- let x=t1 in t2 : T2

対
^^

ここまでの関数プログラミングの例では、値の対(*pairs*)を頻繁に使ってきました。そのような対の型は直積型(*product
type*)と呼ばれます。

対の形式化はほとんど議論する余地がないほど簡単です。しかし、共通パターンを強調するため、定義のいろいろな部分をちょっと見てみましょう。

Coqでは、対の構成要素を抽出する基本的な方法は、パターンマッチング(*pattern
matching*)です。別の方法としては、\ ``fst``\ と\ ``snd``\ 、つまり、1番目と2番目の要素の射影操作を基本操作として持つ方法があります。お遊びで、直積をこの方法でやってみましょう。例えば、数値の対をとり、その和と差の対を返す関数の書き方は次の通りです:

::

           \x:Nat*Nat.
              let sum = x.fst + x.snd in
              let diff = x.fst - x.snd in
              (sum,diff)

これから、単純型付きラムダ計算に対を追加するには、2つの新しい項の形を追加することが含まれます。1つは対で\ ``(t1,t2)``\ と書きます。もう1つは射影で、第1射影は\ ``t.fst``\ 、第2射影は\ ``t.snd``\ と書きます。さらに1つの型コンストラクタ\ ``T1*T2``\ を追加します。これは\ ``T1``\ と\ ``T2``\ の直積と呼びます。

構文:

::

           t ::=                項
               | ...
               | (t,t)             対
               | t.fst             第1射影
               | t.snd             第2射影

           v ::=                値
               | ...
               | (v,v)             対値

           T ::=                型
               | ...
               | T * T             直積型

評価については、対と射影がどう振る舞うかを規定するいくつかの新しい規則が必要です。

::

                                  t1 ==> t1'
                             --------------------                        (ST_Pair1)
                             (t1,t2) ==> (t1',t2)

                                  t2 ==> t2'
                             --------------------                        (ST_Pair2)
                             (v1,t2) ==> (v1,t2')

                                  t1 ==> t1'
                              ------------------                          (ST_Fst1)
                              t1.fst ==> t1'.fst

                              ------------------                       (ST_FstPair)
                              (v1,v2).fst ==> v1

                                  t1 ==> t1'
                              ------------------                          (ST_Snd1)
                              t1.snd ==> t1'.snd

                              ------------------                       (ST_SndPair)
                              (v1,v2).snd ==> v2

規則\ ``ST_FstPair``\ と\ ``ST_SndPair``\ は、完全に評価された対が第1射影または第2射影に遭遇したとき、結果が対応する要素であることを規定します。合同規則\ ``ST_Fst1``\ と\ ``ST_Snd1``\ は、射影の対象の項が完全に評価されきっていないとき、その簡約を認めるものです。\ ``ST_Pair1``\ と\ ``ST_Pair2``\ は対の構成部分の評価です。最初に左の部分を評価し、それが値を持ったら、次に右の部分を評価します。これらの規則内でメタ変数\ ``v``\ と\ ``t``\ を使うことで現れる順番は、対を左から右の順で評価すること(left-to-right
evaluation)を規定しています。(暗黙の慣習として、\ ``v``\ や\ ``v1``\ などのメタ変数は値のみを指すものとしています。)また値の定義に節を加え、\ ``(v1,v2)``\ が値であることを規定しています。対値の要素自体が値でなければならないという事実は、関数の引数として渡された対が、関数の本体の実行が開始される前に完全に評価されることを保証します。

対と射影の型付け規則はそのまま直ぐに得られます。

::

                   Gamma |- t1 : T1       Gamma |- t2 : T2
                   ---------------------------------------                 (T_Pair)
                           Gamma |- (t1,t2) : T1*T2

                            Gamma |- t1 : T11*T12
                            ---------------------                           (T_Fst)
                            Gamma |- t1.fst : T11

                            Gamma |- t1 : T11*T12
                            ---------------------                           (T_Snd)
                            Gamma |- t1.snd : T12

規則\ ``T_Pair``\ は、\ ``t1``\ が型\ ``T1``\ を持ち、\ ``t2``\ が型\ ``T2``\ を持つならば、\ ``(t1,t2)``\ が型\ ``T1*T2``\ を持つことを言っています。逆に、規則\ ``T_Fst``\ と\ ``T_Snd``\ は、\ ``t1``\ が直積型\ ``T11*T12``\ を持つ(つまり評価結果が対になる)ならば、射影の型は\ ``T11``\ と\ ``T12``\ になることを定めます。

直和
^^^^

多くのプログラムでは2つの異なった形を持つ値を扱うことが求められます。例えばアカウント処理をするアプリケーションで名前か、「または」、IDナンバーで雇用者を認証するかもしれません。探索関数はマッチした値か、「または」、エラーコードを返すかもしれません。

これらは、(2項の)直和型(*sum
type*)の例です。(2項)直和型は2つの与えられた型から抽出した値の集合にあたります。例えば

::

           Nat + Bool

この型の要素を、それぞれの構成部分の型の要素にタグ付けする(*tagging*)ことで生成します。例えば、\ ``n``\ が\ ``Nat``\ ならば\ ``inl v``\ は\ ``Nat+Bool``\ の要素です。同様に、\ ``b``\ が\ ``Bool``\ ならば\ ``inr b``\ は\ ``Nat+Bool``\ の要素です。タグの名前\ ``inl``\ と\ ``inr``\ は、これらのタグを関数と考えるところから出ています。

::

       inl : Nat -> Nat + Bool
       inr : Bool -> Nat + Bool

これらの関数は、\ ``Nat``\ または\ ``Bool``\ の要素を直和型\ ``Nat+Bool``\ の左部分または右部分に単射("inject")します。(しかし、実際にはこれらを関数としては扱いません。\ ``inl``\ と\ ``inr``\ はキーワードで、\ ``inl t``\ と\ ``inr t``\ は基本構文形であり、関数適用ではありません。この扱いによって、これらに特別な型付け規則を用意できるようになります。)

一般に、型\ ``T1 + T2``\ の要素は\ ``T1``\ の要素に\ ``inl``\ をタグ付けしたものと、\ ``T2``\ の要素に\ ``inr``\ をタグ付けしたものから成ります。

直和型の要素を「使う」目的で、その分解のために\ ``case``\ 構文を導入します(これはCoqの\ ``match``\ の非常に単純化された形です)。例えば、以下の手続きは、\ ``Nat+Bool``\ を\ ``Nat``\ に変換します:

::

        getNat =
          \x:Nat+Bool.
            case x of
              inl n => n
            | inr b => if b then 1 else 0

より形式的に...

構文:

::

           t ::=                項
               | ...
               | inl T t           タグ付け(左)
               | inr T t           タグ付け(右)
               | case t of         case
                   inl x => t
                 | inr x => t

           v ::=                値
               | ...
               | inl T v           タグ付き値(左)
               | inr T v           タグ付き値(右)

           T ::=                型
               | ...
               | T + T             直和型

評価:

::

                                  t1 ==> t1'
                            ----------------------                         (ST_Inl)
                            inl T t1 ==> inl T t1'

                                  t1 ==> t1'
                            ----------------------                         (ST_Inr)
                            inr T t1 ==> inr T t1'

                                  t0 ==> t0'
                       -------------------------------------------       (ST_Case)
                       case t0 of inl x1 => t1 | inr x2 => t2 ==>
                       case t0' of inl x1 => t1 | inr x2 => t2

                ----------------------------------------------         (ST_CaseInl)
                case (inl T v0) of inl x1 => t1 | inl x2 => t2
                               ==>  [v0/x1] t1

                ----------------------------------------------         (ST_CaseInr)
                case (inr T v0) of inl x1 => t1 | inl x2 => t2
                               ==>  [v0/x2] t2

型付け:

::

                              Gamma |- t1 :  T1
                         ----------------------------                       (T_Inl)
                         Gamma |- inl T2 t1 : T1 + T2

                               Gamma |- t1 : T2
                         ----------------------------                       (T_Inr)
                         Gamma |- inr T1 t1 : T1 + T2

                             Gamma |- t0 : T1+T2
                           Gamma , x1:T1 |- t1 : T
                           Gamma , x2:T2 |- t2 : T
             ---------------------------------------------------           (T_Case)
             Gamma |- case t0 of inl x1 => t1 | inr x2 => t2 : T

``inl``\ と\ ``inr``\ の形に型を付記する理由は、型の一意性を保つためです。この情報がなければ、型推論規則\ ``T_Inl``\ は、例えば、\ ``t1``\ が型\ ``T1``\ の要素であることを示した後、「任意の」型\ ``T2``\ について\ ``inl t1``\ が\ ``T1 + T2``\ の要素であることを導出できます。例えば、\ ``inl 5 : Nat + Nat``\ と\ ``inl 5 : Nat + Bool``\ の両方(および無限に多数の他の型付け)が導出できます。この型の一意性の失敗は、型チェックアルゴリズムを、ここまでやってきたように「規則を下から上に読む」という単純な方法で構築することができなくなることを意味します。

この問題を扱うのにはいろいろな方法があります。簡単なものの1つは、ここで採用する方法ですが、単射を実行するときに直和型の「別の側」をプログラマが明示的に付記することを強制するというものです。これはプログラマにとってかなりヘビーウェイトです(そのため実際の言語は別の解法を採用しています)。しかし、理解と形式化は容易な方法です。

リスト
^^^^^^

ここまで見てきた型付け機能は、\ ``Bool``\ のような基本型(*base
types*)と、古い型から新しい型を構築する\ ``->``\ や\ ``*``\ のような型コンストラクタ(*type
constructors*)に分類できます。もう一つの有用な型コンストラクタが\ ``List``\ です。すべての型\ ``T``\ について、型\ ``List T``\ は\ ``T``\ から抽出したものを要素とする有限長リストを表します。

原理的には、リストの機構を使って、バリアントを定義したり、再帰型(*recursive*
types)を定義したりすることができます。しかし、前者の詳細はここまで省略してきており、後者に意味を与えることは簡単ではありません。その代わりに、リストの特別な場合を直接議論します。

以下にリストの構文、意味、型付け規則を与えます。\ ``nil``\ に対して明示的に型を付記することが必須であり、\ ``cons``\ には付記できないという点を除けば、ここで定義されたリストは本質的にCoqで構築したものと同じです。リストを分解するために\ ``lcase``\ を使います。これは「空リストの\ ``head``\ は何か？」というような問題を扱うことを避けるためです。従って、例えば、数値リストの最初の2つの要素の和を計算する関数は次の通りです:

::

        \x:List Nat.
        lcase x of nil -> 0
           | a::x' -> lcase x' of nil -> a
                         | b::x'' -> a+b

``cons v1 v2``\ が値というときには、\ ``v2``\ もリストでなければなりません。値の形式的定義ではこのことを強制します。

構文:

::

           t ::=                Terms
               | ...
               | nil T
               | cons t t
               | lcase t of nil -> t | x::x -> t

           v ::=                Values
               | ...
               | nil T             nil value
               | cons v v          cons value

           T ::=                Types
               | ...
               | List T            list of Ts

簡約:

::

                                     t1 ==> t1'
                           --------------------------                    (ST_Cons1)
                           cons t1 t2 ==> cons t1' t2

                                     t2 ==> t2'
                           --------------------------                    (ST_Cons2)
                           cons v1 t2 ==> cons v1 t2'

                                  t1 ==> t1'
                    ----------------------------------------             (ST_Lcase1)
                    (lcase t1 of nil -> t2 | h::t -> t3) ==>
                    (lcase t1' of nil -> t2 | h::t -> t3)

                   ---------------------------------------            (ST_LcaseNil)
                   (lcase nil T of nil -> t2 | h::t -> t3)
                                    ==> t2

                ----------------------------------------------       (ST_LcaseCons)
                (lcase (cons vh vt) of nil -> t2 | h::t -> t3)
                              ==> [vh/h,vt/t]t3

型付け:

::

                              -----------------------                       (T_Nil)
                              Gamma |- nil T : List T

                    Gamma |- t1 : T      Gamma |- t2 : List T
                    -----------------------------------------              (T_Cons)
                           Gamma |- cons t1 t2: List T

                            Gamma |- t1 : List T1
                               Gamma |- t2 : T
                       Gamma , h:T1, t:List T1 |- t3 : T
              -------------------------------------------------           (T_Lcase)
              Gamma |- (lcase t1 of nil -> t2 | h::t -> t3) : T

一般再帰
^^^^^^^^

(Coqを含む)ほとんどのプログラミング言語に現れるもう1つの機構が、再帰関数を定義する機能です。例えば、階乗関数を次のように定義できるとよいと思うでしょう:

::

       fact = \x:Nat.
                 if x=0 then 1 else x * (fact (pred x)))

しかし、これを形式化するには、なかなかの作業が必要になります。そうするには、「関数定義」("function
definitions")の概念を導入し、\ ``step``\ の定義の中で、関数定義の「環境」("environment")を持ち回ることが必要になるでしょう。

ここでは、直接的に形式化する別の方法をとります。右辺に定義しようとしている識別子を含む再帰的定義を書く代わりに、不動点演算子(*fixed-point
operator*)を定義することができます。不動点演算子は、簡約の過程で再帰的定義の右辺を遅延(lazy)して「展開」("unfold")するものです。

::

       fact =
           fix
             (\f:Nat->Nat.
                \x:Nat.
                   if x=0 then 1 else x * (f (pred x)))

直観的には\ ``fix``\ に渡される高階関数\ ``f``\ は\ ``fact``\ 関数の生成器(*generator*)です。\ ``f``\ が、\ ``fact``\ に求められる振る舞いを\ ``n``\ まで近似する関数(つまり、\ ``n``\ 以下の入力に対して正しい結果を返す関数)に適用されるとき、\ ``f``\ はより良い近似、つまり、\ ``n+1``\ まで正しい答えを返す関数、を返します。\ ``fix``\ をこの生成器に適用すると、生成器の不動点(*fixed
point*)を返します。この不動点は、すべての入力\ ``n``\ について求められる振る舞いをする関数です。

(不動点("fixed
point")という用語は通常の数学とまったく同じ意味で使っています。通常の数学では、関数\ ``f``\ の不動点とは、\ ``f(x) = x``\ となる入力\ ``x``\ のことです。これから、(いってみれば)型\ ``(Nat->Nat)->(Nat->Nat)``\ を持つ関数\ ``F``\ の不動点は、\ ``F f``\ が\ ``f``\ と振る舞い同値である関数\ ``f``\ です。)

構文:

::

           t ::=                項
               | ...
               | fix t             不動点演算子

簡約:

::

                                     t1 ==> t1'
                                 ------------------                       (ST_Fix1)
                                 fix t1 ==> fix t1'

                    -------------------------------------------         (ST_FixAbs)
                    fix (\x:T1.t2) ==> [(fix(\x:T1.t2)) / x] t2

型付け:

::

                                Gamma |- t1 : T1->T1
                                --------------------                        (T_Fix)
                                Gamma |- fix t1 : T1

練習問題: ★ (halve\_fix)
''''''''''''''''''''''''

::

    []
    *)

FILL IN HERE 次の再帰的定義を\ ``fix``\ を用いた定義に直しなさい:

::

       halve =
         \x:Nat.
            if x=0 then 0
            else if (pred x)=0 then 0
            else 1 + (halve (pred (pred x))))

(\* FILL IN HERE \*)☐

練習問題: ★, recommended (fact\_steps)
''''''''''''''''''''''''''''''''''''''

::

    []
    *)

FILL IN HERE
項\ ``fact 1``\ が正規形まで簡約されるステップ列を書き下しなさい(ただし、算術演算については通常の簡約規則を仮定します)。

(\* FILL IN HERE \*)☐

任意の\ ``T``\ について型\ ``T->T``\ の関数の不動点が記述できる形ができたことから、驚くようなことが起こります。特に、すべての型が何らかの項に住まれている(inhabited)ということが導かれます。これを確認するため、すべての型\ ``T``\ について、項

::

        fix (\x:T.x)

が定義できることを見てみましょう。\ ``T_Fix``\ と\ ``T_Abs``\ から、この項は型\ ``T``\ を持ちます。\ ``ST_FixAbs``\ より、この項を簡約すると何度やっても自分自身になります。したがって、この項は\ ``T``\ の未定義要素(*undefined
element*)です。

より有用なこととして、次は\ ``fix``\ を使って2引数の再帰関数を定義する例です:

::

        equal =
          fix
            (\eq:Nat->Nat->Bool.
               \m:Nat. \n:Nat.
                 if m=0 then iszero n
                 else if n=0 then false
                 else eq (pred m) (pred n))

そして最後に、次は\ ``fix``\ を使って再帰関数の対を定義する例です(この例は、規則\ ``T_Fix``\ の型\ ``T1``\ は関数型ではなくてもよいことを示しています):

::

        evenodd =
          fix
            (\eo: (Nat->Bool * Nat->Bool).
               let e = \n:Nat. if n=0 then true  else eo.snd (pred n) in
               let o = \n:Nat. if n=0 then false else eo.fst (pred n) in
               (e,o))

        even = evenodd.fst
        odd  = evenodd.snd

レコードとバリアント (Optional)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

STLCの基本拡張の最後の例として、レコード(*records*)とその型をどのように形式化するかをちょっと見てみましょう。この拡張は概念的には対と直積型の真っ直ぐな一般化ですが、記法的にはちょっとたいへんです。このため、形式的な扱いは独立した章(``Records_J``)まで置いておきます。

この素材は以下の追加の練習問題には含まれません。必要ならば、とばしても斜め読みしても構いません。

``Unit``\ 型
^^^^^^^^^^^^

もう一つの便利な基本型は、MLファミリーの言語に特に見られるものですが、1要素の型\ ``Unit``\ です。この型は要素を1つ持ちます。それは項定数\ ``unit``\ です(先頭の文字は小文字の\ ``u``\ です)。型付け規則は\ ``unit``\ を\ ``Unit``\ の要素と定めます。計算の結果として取りうる値の集合にも\ ``unit``\ を加えます。実際、\ ``unit``\ は型\ ``Unit``\ の式の評価結果としてとり得る唯一の値です。

構文:

::

           t ::=                項
               | ...
               | unit              unit値

           v ::=                値
               | ...
               | unit              unit

           T ::=                型
               | ...
               | Unit              Unit型

型付け:

::

                             --------------------                          (T_Unit)
                             Gamma |- unit : Unit

単に1つだけの要素を持つ型を定義することにわずらわされるのは、少々奇妙なことに見えるかもしれません。何と言っても、このような型の中の計算はどうでも良いものだけではないのでしょうか？

これは妥当な質問です。実際STLCでは\ ``Unit``\ 型は特別、問題ではありません(ちょっと後でこの型のある使い道を見ることになりますが)。\ ``Unit``\ が本当に便利なのはよりリッチな言語でいろいろな種類の副作用(*side
effects*)を持つ場合です。例えば、変更可能な変数やポインタについての代入文や、例外その他のローカルではないコントロール機構を持つ場合、などです。そのような言語では、副作用のためだけに評価される式の(どうでもよい)結果のための型が便利なのです。

レコード
^^^^^^^^

日常的なプログラミング言語のもう1つの馴染み深い構造が、レコード(*records*)です。直観的には、レコードは2種類の一般化の組み合わせによって得られます。1つは(2項だけではなく)n-項積です。もう1つはフィールドアクセスに(場所ではなく)ラベル(*label*)を使うことです。

構文:

::

           t ::=                          項
               | ...
               | {i1=t1, ..., in=tn}         レコード
               | t.i                         射影

           v ::=                          値
               | ...
               | {i1=v1, ..., in=vn}         レコード値

           T ::=                          型
               | ...
               | {i1:T1, ..., in:Tn}         レコード型

直観的には、この一般化はかなり明確です。しかし、ここで実際に記述したものはかなり非形式的であることは注意しておくべきです。特に、いろいろなところで、"``...``\ "を「これらを何個か」という意味で使っていますし、レコードに同じラベルが複数回出てきてはいけない、という通常の付加条件を明示的に述べることを省いています。より詳細な非形式的記法を考案することもできますが、それはかなりヘビーで、また定義の大事な点をわかりにくくすることになりかねません。このため、ここではちょっとルーズなまま残しておいて(とにかく、どちらにしろ非形式的なのです)、きっちり仕上げるのは別のところ(``Records_J.v``)でやります。

簡約:

::

                                  ti ==> ti'
                     ------------------------------------                  (ST_Rcd)
                         {i1=v1, ..., im=vm, in=ti, ...}
                     ==> {i1=v1, ..., im=vm, in=ti', ...}

                                  t1 ==> t1'
                                --------------                           (ST_Proj1)
                                t1.i ==> t1'.i

                          -------------------------                    (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi

再び、これらの規則はちょっと非形式的です。例えば、最初の規則は「\ ``ti``\ が値でないフィールドのうち最も左のもので、\ ``ti``\ は\ ``ti'``\ にステップで進むならば、レコード全体のステップは...」と読まれることを意図しています。最後の規則では、i
と呼ばれるフィールドは1つだけで、他のすべてのフィールドは値を持っていることを意図しています。

型付け:

::

                Gamma |- t1 : T1     ...     Gamma |- tn : Tn
              --------------------------------------------------            (T_Rcd)
              Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                        Gamma |- t : {..., i:Ti, ...}
                        -----------------------------                      (T_Proj)
                              Gamma |- t.i : Ti

レコードのエンコード
^^^^^^^^^^^^^^^^^^^^

上述の定義を精密にするにはいろいろな方法があります。

-  構文の形と推論規則を、上記の形になるべく近いまま直接形式化するという方法があります。
   これは概念的に「直球」で、もし本当のコンパイラを作るならば、おそらくいちばん合っているでしょう。特に、形式化の中にエラーメッセージのプリントを含めることができるので、プログラマが理解するのが容易になるでしょう。しかし、規則の形式化版はまったくきれいにはなりません!
-  レコードを表現する、よりスムーズな方法を探すことができます。
   例えば、1つのコンストラクタでレコード全体を一度に作るのではなく、空レコードに対応する1つのコンストラクタと、存在するレコードに1つのフィールドを追加する別のコンストラクタの2つで表現するという方法があります。この方法は、レコードについての計算のメタ理論に一番の興味がある場合には正しい方法です。なぜなら、この方法をとると、きれいで優雅な定義と証明が得られるからです。ファイル\ ``Records_J.v``\ では、この方法がどのように行えるかを示しています。
-  別の方法として、望むならば、レコードを形式化することを完全に避けることができます。
   このためには、レコード記法は、対と直積型を含むより複雑な式の単なる非形式的な略記法である、と規定します。ここではこのアプローチのスケッチを与えます。

最初に、任意のサイズの組が対と\ ``unit``\ 値のネストでエンコードできることを確認します。対の記法\ ``(t1,t2)``\ を混用するのを避けるため、組を書き下すためにはラベルを持たない中カッコ(``{..}``)を使います。これから、\ ``{}``\ は0個組、\ ``{5}``\ は一つ組、\ ``{5,6}``\ は二つ組(おそらく対と同じ)、\ ``{5,6,7}``\ は三つ組、等です。

::

        {}                 ---->  unit
        {t1, t2, ..., tn}  ---->  (t1, trest)
                                  ただし {t2, ..., tn} ----> trest

同様に、組の型を直積型のネストでエンコードすることができます。

::

        {}                 ---->  Unit
        {T1, T2, ..., Tn}  ---->  T1 * TRest
                                  ただし {T2, ..., Tn} ----> TRest

組のフィールドの射影演算は、第2射影の列に続く第1射影としてエンコードできます:

::

        t.0        ---->  t.fst
        t.(n+1)    ---->  (t.snd).n

次に、レコードラベルに何らかの全順序があり、そのため各ラベルに一意に自然数が関連づけられると仮定します。この数をラベルのポジション(*position*)と呼びます。例えば、以下のようにポジションが定められるとします:

::

          LABEL   POSITION
          a       0
          b       1
          c       2
          ...     ...
          foo     1004
          ...     ...
          bar     10562
          ...     ...

このポジションを、レコード値を組(つまりネストされた対)でエンコードするために使います。つまり、フィールドをそのポジションでソートします。例えば:

::

          {a=5, b=6}      ---->   {5,6}
          {a=5, c=7}      ---->   {5,unit,7}
          {c=7, a=5}      ---->   {5,unit,7}
          {c=5, b=3}      ---->   {unit,3,5}
          {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
          {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}

以下のことに注意します。各フィールドはそのラベルに関連づけられたポジションに現れます。また、組の大きさは、最大のポジションを持つラベルによって決定されます。そして、使われていないポジションは\ ``unit``\ で埋められます。

レコードの型についてもまったくおなじことをします:

::

          {a:Nat, b:Nat}      ---->   {Nat,Nat}
          {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat}
          {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}

最後に、レコードの射影は適切なポジションについての組の射影でエンコードされます:

::

          t.l  ---->  t.(position of l)

レコードのオリジナルの「直接の」表現に対するすべての型付け規則が、このエンコードで正しいことをチェックするのは難しいことではありません。(簡約規則は正しさを「ほぼ」確認できます。完全に、ではありません。なぜなら、フィールドの並べ直しのエンコードのためです。)

もちろん、ラベル\ ``bar``\ を持つレコードをたまたま使ったときには、このエンコードはあまり効率的ではありません。しかしこの問題は見た目ほど深刻ではありません。もし、コンパイラがプログラム全体を同時に見ることができると仮定するなら、ラベルの番号づけをうまく選んで、一番よく使われるラベルに小さいポジションを与えることができます。実際、商用のコンパイラで本質的にこれをやっているものがあります!

バリアント
^^^^^^^^^^

直積がレコードに一般化できたのと同様、直和は
n-個のラベルを持った型「バリアント」(*variants*)に一般化できます。\ ``T1+T2``\ の代わりに\ ``<l1:T1,l2:T2,...ln:Tn>``\ のように書くことができます。ここで\ ``l1``\ 、\ ``l2``\ 、...
はフィールドラベルで、インスタンスの構成と、case
のラベルの両方に使われます。

n-個のバリアントは、リストや木構造のような任意の帰納的データ型をゼロから構築するのに必要なメカニズムのほとんどを与えます。唯一足りないのは、型定義の再帰です。ここではこの話題は扱いません。ただ、詳細な扱いはいろいろなテキストブックに書かれています。例えば
"Types and Programming Languages" です。

拡張を形式化する
----------------

練習問題: ★★★★, recommended (STLC\_extensions)
''''''''''''''''''''''''''''''''''''''''''''''

拡張(オプションの1つを除く)の形式化は読者に残してあります。項と型の構文の必要な拡張は提示しておきました。また、読者が、自分の定義が期待された通りに動作するかをテストすることができるように、いくつかの例を示しておきました。読者は定義の残りの部分を埋め、それに合わせて証明を拡張しなさい。(訳注：節構成がまぎらわしいですが、この章のここ以降はすべてこの練習問題の内部のようです。埋めるのはその中の「ここを埋めなさい」という部分です。なお、以下の記述はCoq記述内の埋め込みコメントを読まないと理解できない部分があると思いますが、HTML化したものでは、埋め込みコメントが表示されていないかもしれません。その場合はHTML化前のCoqソースを見てください。)

よい戦略は、ファイルの最初から最後までを1パスで行おうとせずに、複数回のパスで拡張項目を一つづつやることです。定義または証明のそれぞれについて、提示されたパーツを注意深く読むことから始めなさい。その際に、ハイレベルの直観については\ ``Stlc_J``\ 章のテキストを参照し、詳細の機構については、埋め込まれたコメントを参照しなさい。

拡張を試みる良い順番は以下の順でしょう:

-  最初に数値(なぜなら、馴染み深く簡単なので)
-  直積
-  let (束縛を含むので)
-  直和 (より複雑な束縛を含むので)
-  リスト (さらに複雑な束縛を含むので)
-  ``fix``

   Module STLCExtended.

構文と操作的意味
^^^^^^^^^^^^^^^^

::

    Inductive ty : Type :=
      | ty_arrow : ty -> ty -> ty
      | ty_prod  : ty -> ty -> ty
      | ty_sum   : ty -> ty -> ty
      | ty_List  : ty -> ty
      | ty_Nat   : ty.

    Tactic Notation "ty_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ty_arrow"
      | Case_aux c "ty_prod" | Case_aux c "ty_sum"
      | Case_aux c "ty_List" | Case_aux c "ty_Nat" ].

    Inductive tm : Type :=


      (* 拡張されていないSTLC *)

    | tm_var : id -> tm
      | tm_app : tm -> tm -> tm
      | tm_abs : id -> ty -> tm -> tm


      (* 対 *)

    | tm_pair : tm -> tm -> tm
      | tm_fst : tm -> tm
      | tm_snd : tm -> tm


      (* 直和 *)

    | tm_inl : ty -> tm -> tm
      | tm_inr : ty -> tm -> tm
      | tm_case : tm -> id -> tm -> id -> tm -> tm


              (* 例えば、[case t0 of inl x1 => t1 | inr x2 => t2] *)


      (* リスト *)

    | tm_nil : ty -> tm
      | tm_cons : tm -> tm -> tm
      | tm_lcase : tm -> tm -> id -> id -> tm -> tm


              (* 例えば、[lcase t1 of | nil -> t2 | x::y -> t3] *)


      (* 数値 *)

    | tm_nat : nat -> tm
      | tm_succ : tm -> tm
      | tm_pred : tm -> tm
      | tm_mult : tm -> tm -> tm
      | tm_if0  : tm -> tm -> tm -> tm


      (* let *)

    | tm_let : id -> tm -> tm -> tm


              (* 例えば、[let x = t1 in t2] *)


      (* fix *)

    | tm_fix  : tm -> tm.

なお、簡潔にするため、ブール値をなくし、その代わりゼロテストと条件分岐を組み合わせた\ ``if0``\ 構文を提供してきています。つまり、

::

           if x = 0 then ... else ...

と書く代わりに、次のように書きます:

::

           if0 x then ... else ...

    Tactic Notation "tm_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
      | Case_aux c "tm_pair" | Case_aux c "tm_fst" | Case_aux c "tm_snd"
      | Case_aux c "tm_inl" | Case_aux c "tm_inr" | Case_aux c "tm_case"
      | Case_aux c "tm_nil" | Case_aux c "tm_cons" | Case_aux c "tm_lcase"
      | Case_aux c "tm_nat" | Case_aux c "tm_succ" | Case_aux c "tm_pred"
      | Case_aux c "tm_mult" | Case_aux c "tm_if0"
      | Case_aux c "tm_let" | Case_aux c "tm_fix" ].

置換
^^^^

::

    Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
      match t with
      | tm_var y =>
          if beq_id x y then s else t
      | tm_abs y T t1 =>
          tm_abs y T (if beq_id x y then t1 else (subst x s t1))
      | tm_app t1 t2 =>
          tm_app (subst x s t1) (subst x s t2)
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    | _ => t


      (* ...そして上の行を消しなさい。 *)

    end.

簡約
^^^^

次にこの言語の値を定義します。

::

    Inductive value : tm -> Prop :=
      | v_abs : forall x T11 t12,
          value (tm_abs x T11 t12)
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

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
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    where "t1 '==>' t2" := (step t1 t2).

    Tactic Notation "step_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
        (* FILL IN HERE *)


        (* ここを埋めなさい *)

    ].

    Notation stepmany := (refl_step_closure step).
    Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

    Hint Constructors step.

型付け
^^^^^^

::

    Definition context := partial_map ty.

次に型付け規則を定義します。上述の推論規則のほとんど直接の転写です。

::

    Inductive has_type : context -> tm -> ty -> Prop :=

      | T_Var : forall Gamma x T,
          Gamma x = Some T ->
          has_type Gamma (tm_var x) T
      | T_Abs : forall Gamma x T11 T12 t12,
          has_type (extend Gamma x T11) t12 T12 ->
          has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
      | T_App : forall T1 T2 Gamma t1 t2,
          has_type Gamma t1 (ty_arrow T1 T2) ->
          has_type Gamma t2 T1 ->
          has_type Gamma (tm_app t1 t2) T2
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    .

    Hint Constructors has_type.

    Tactic Notation "has_type_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
        (* FILL IN HERE *)


        (* ここを埋めなさい *)

    ].

例
~~

この節では上述の例(および追加のいくつか)の形式化版を示します。最初の方のものは、特定の拡張項目に焦点を当てています。ファイルの後の方の、その拡張項目について証明を拡張するところに進む前に、これらの例を使って拡張項目についての自分の定義が適切かを確認することができます。後の方の例はいろいろな拡張項目をまとめて必要とします。すべての定義を埋めた後、これらの例に戻ってみる必要があるでしょう。

::

    Module Examples.

準備
^^^^

最初に、いくつか変数名を定義しましょう:

::

    Notation a := (Id 0).
    Notation f := (Id 1).
    Notation g := (Id 2).
    Notation l := (Id 3).
    Notation k := (Id 6).
    Notation i1 := (Id 7).
    Notation i2 := (Id 8).
    Notation x := (Id 9).
    Notation y := (Id 10).
    Notation processSum := (Id 11).
    Notation n := (Id 12).
    Notation eq := (Id 13).
    Notation m := (Id 14).
    Notation evenodd := (Id 15).
    Notation even := (Id 16).
    Notation odd := (Id 17).
    Notation eo := (Id 18).

次に、Coq
にちょっと手を入れて、型の導出の検索を自動化します。詳細を理解する必要はまったくありません。ざっと眺めておけば、もし\ ``auto``\ に独自の拡張をしなければならなくなったとき、何を調べれば良いかがわかるでしょう。

以下の\ ``Hint``\ 宣言は、次のように言っています:``auto``\ が\ ``(has_type G (tm_app e1 e2) T)``\ という形のゴールに到達したときは常に、\ ``eapply T_App``\ を考えなさい。この結果、中間的な型
T1
の存在変数が残ります。(コメントになっている)\ ``lcase``\ についても同様です。その存在変数は、\ ``e1``\ と\ ``e2``\ の型導出の探索の仮定で具体化されます。またヒントに、等号による比較の形のゴールを解く場合に「より困難なことを試しなさい」ということも追加します。これは、\ ``T_Var``\ (これは事前条件に等号による比較を含みます)を自動的に使用するのに便利です。

::

    Hint Extern 2 (has_type _ (tm_app _ _) _) =>
      eapply T_App; auto.


    (* 型関係に[T_Lcase]を定義した後では、次の部分のコメントをはずすのが良いでしょう。 *)


    (* 
    Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
      eapply T_Lcase; auto.
    *)

    Hint Extern 2 (_ = _) => compute; reflexivity.

数値
^^^^

::

    Module Numtest.

``if0 (pred (succ (pred (2 * 0)))) then 5 else 6``

::

    Definition test :=
      tm_if0
        (tm_pred
          (tm_succ
            (tm_pred
              (tm_mult
                (tm_nat 2)
                (tm_nat 0)))))
        (tm_nat 5)
        (tm_nat 6).




      auto 10.
    Qed.

    Example numtest_reduces :
      test ==>* tm_nat 5.
    Proof.
      unfold test. normalize.
    Qed.
    *)

動くだけ定義が十分に行えたと思ったなら、以降の\ ``Example``\ のコメントをはずしなさい。

::

    (*
    Example typechecks :
      has_type (@empty ty) test ty_Nat.
    Proof.
      unfold test.
      (* この型導出は非常に深く、そのため[auto]の最大探索深度を、
         デフォルトの5から10に上げなければなりません。 *)
      auto 10.
    Qed.

    Example numtest_reduces :
      test ==>* tm_nat 5.
    Proof.
      unfold test. normalize.
    Qed.
    *)

    End Numtest.

直積
^^^^

::

    Module Prodtest.

``((5,6),7).fst.snd``

::

    Definition test :=
      tm_snd
        (tm_fst
          (tm_pair
            (tm_pair
              (tm_nat 5)
              (tm_nat 6))
            (tm_nat 7))).


    (*
    Example typechecks :
      has_type (@empty ty) test ty_Nat.
    Proof. unfold test. eauto 15. Qed.

    Example reduces :
      test ==>* tm_nat 6.
    Proof. unfold test. normalize. Qed.
    *)

    End Prodtest.

``let``
^^^^^^^

::

    Module LetTest.

``let x = pred 6 in succ x``

::

    Definition test :=
      tm_let
        x
        (tm_pred (tm_nat 6))
        (tm_succ (tm_var x)).


    (*
    Example typechecks :
      has_type (@empty ty) test ty_Nat.
    Proof. unfold test. eauto 15. Qed.

    Example reduces :
      test ==>* tm_nat 6.
    Proof. unfold test. normalize. Qed.
    *)

    End LetTest.

直和
^^^^

::

    Module Sumtest1.

[case (inl Nat 5) ofinl x => x\| inr y => y]

::

    Definition test :=
      tm_case (tm_inl ty_Nat (tm_nat 5))
        x (tm_var x)
        y (tm_var y).


    (*
    Example typechecks :
      has_type (@empty ty) test ty_Nat.
    Proof. unfold test. eauto 15. Qed.

    Example reduces :
      test ==>* (tm_nat 5).
    Proof. unfold test. normalize. Qed.
    *)

    End Sumtest1.

    Module Sumtest2.

[let processSum =:Nat+Nat.case x ofinl n => ninr n => if0 n then 1 else
0 in(processSum (inl Nat 5), processSum (inr Nat 5))]

::

    Definition test :=
      tm_let
        processSum
        (tm_abs x (ty_sum ty_Nat ty_Nat)
          (tm_case (tm_var x)
             n (tm_var n)
             n (tm_if0 (tm_var n) (tm_nat 1) (tm_nat 0))))
        (tm_pair
          (tm_app (tm_var processSum) (tm_inl ty_Nat (tm_nat 5)))
          (tm_app (tm_var processSum) (tm_inr ty_Nat (tm_nat 5)))).


    (*
    Example typechecks :
      has_type (@empty ty) test (ty_prod ty_Nat ty_Nat).
    Proof. unfold test. eauto 15. Qed.

    Example reduces :
      test ==>* (tm_pair (tm_nat 5) (tm_nat 0)).
    Proof. unfold test. normalize. Qed.
    *)

    End Sumtest2.

リスト
^^^^^^

::

    Module ListTest.

[let l = cons 5 (cons 6 (nil Nat)) inlcase l ofnil => 0\| x::y => x\*x]

::

    Definition test :=
      tm_let l
        (tm_cons (tm_nat 5) (tm_cons (tm_nat 6) (tm_nil ty_Nat)))
        (tm_lcase (tm_var l)
           (tm_nat 0)
           x y (tm_mult (tm_var x) (tm_var x))).


    (*
    Example typechecks :
      has_type (@empty ty) test ty_Nat.
    Proof. unfold test. eauto 20. Qed.

    Example reduces :
      test ==>* (tm_nat 25).
    Proof. unfold test. normalize. Qed.
    *)

    End ListTest.

``fix``
^^^^^^^

::

    Module FixTest1.

[fact := fix(:nat->nat.:nat.if a=0 then 1 else a \* (f (pred a)))]

::

    Definition fact :=
      tm_fix
        (tm_abs f (ty_arrow ty_Nat ty_Nat)
          (tm_abs a ty_Nat
            (tm_if0
               (tm_var a)
               (tm_nat 1)
               (tm_mult
                  (tm_var a)
                  (tm_app (tm_var f) (tm_pred (tm_var a))))))).

(ワーニング:``fact``\ の型チェックが通るかもしれませんが、それでもいくつかの規則が間違ったままです。)

::

    (*
    Example fact_typechecks :
      has_type (@empty ty) fact (ty_arrow ty_Nat ty_Nat).
    Proof. unfold fact. auto 10.
    Qed.
    *)


    (*
    Example fact_example:
      (tm_app fact (tm_nat 4)) ==>* (tm_nat 24).
    Proof. unfold fact. normalize. Qed.
    *)

    End FixTest1.

    Module FixTest2.

[map :=:nat->nat.fix(:``nat``->\ ``nat``.:``nat``.case l of\|☐ ->☐ \|
x::l -> (g x)::(f l))]

::

    Definition map :=
      tm_abs g (ty_arrow ty_Nat ty_Nat)
        (tm_fix
          (tm_abs f (ty_arrow (ty_List ty_Nat) (ty_List ty_Nat))
            (tm_abs l (ty_List ty_Nat)
              (tm_lcase (tm_var l)
                (tm_nil ty_Nat)
                a l (tm_cons (tm_app (tm_var g) (tm_var a))
                             (tm_app (tm_var f) (tm_var l))))))).


    Example map_typechecks :
      has_type empty map
        (ty_arrow (ty_arrow ty_Nat ty_Nat)
          (ty_arrow (ty_List ty_Nat)
            (ty_List ty_Nat))).
    Proof. unfold map. auto 10. Qed.

    Example map_example :
      tm_app (tm_app map (tm_abs a ty_Nat (tm_succ (tm_var a))))
             (tm_cons (tm_nat 1) (tm_cons (tm_nat 2) (tm_nil ty_Nat)))
      ==>* (tm_cons (tm_nat 2) (tm_cons (tm_nat 3) (tm_nil ty_Nat))).
    Proof. unfold map. normalize. Qed.
    *)


    (* 
    (* 上記の最後の [Hint Extern] のコメントが外されていることを確認すること... *)
    Example map_typechecks :
      has_type empty map
        (ty_arrow (ty_arrow ty_Nat ty_Nat)
          (ty_arrow (ty_List ty_Nat)
            (ty_List ty_Nat))).
    Proof. unfold map. auto 10. Qed.

    Example map_example :
      tm_app (tm_app map (tm_abs a ty_Nat (tm_succ (tm_var a))))
             (tm_cons (tm_nat 1) (tm_cons (tm_nat 2) (tm_nil ty_Nat)))
      ==>* (tm_cons (tm_nat 2) (tm_cons (tm_nat 3) (tm_nil ty_Nat))).
    Proof. unfold map. normalize. Qed.
    *)

    End FixTest2.

    Module FixTest3.

[equal =fix(:Nat->Nat->Bool.:Nat. :Nat.if0 m then (if0 n then 1 else
0)else if0 n then 0else eq (pred m) (pred n))]

::

    Definition equal :=
      tm_fix
        (tm_abs eq (ty_arrow ty_Nat (ty_arrow ty_Nat ty_Nat))
          (tm_abs m ty_Nat
            (tm_abs n ty_Nat
              (tm_if0 (tm_var m)
                (tm_if0 (tm_var n) (tm_nat 1) (tm_nat 0))
                (tm_if0 (tm_var n)
                  (tm_nat 0)
                  (tm_app (tm_app (tm_var eq)
                                  (tm_pred (tm_var m)))
                          (tm_pred (tm_var n)))))))).


    (*
    Example equal_typechecks :
      has_type (@empty ty) equal (ty_arrow ty_Nat (ty_arrow ty_Nat ty_Nat)).
    Proof. unfold equal. auto 10.
    Qed.
    *)

    (*
    Example equal_example1:
      (tm_app (tm_app equal (tm_nat 4)) (tm_nat 4)) ==>* (tm_nat 1).
    Proof. unfold equal. normalize. Qed.
    *)

    (*
    Example equal_example2:
      (tm_app (tm_app equal (tm_nat 4)) (tm_nat 5)) ==>* (tm_nat 0).
    Proof. unfold equal. normalize. Qed.
    *)

    End FixTest3.

    Module FixTest4.

[let evenodd =fix(: (Nat->Nat \* Nat->Nat).let e = :Nat. if0 n then 1
else eo.snd (pred n) inlet o = :Nat. if0 n then 0 else eo.fst (pred n)
in(e,o)) inlet even = evenodd.fst inlet odd = evenodd.snd in(even 3,
even 4)]

::

    Definition eotest :=
      tm_let evenodd
        (tm_fix
          (tm_abs eo (ty_prod (ty_arrow ty_Nat ty_Nat) (ty_arrow ty_Nat ty_Nat))
            (tm_pair
              (tm_abs n ty_Nat
                (tm_if0 (tm_var n)
                  (tm_nat 1)
                  (tm_app (tm_snd (tm_var eo)) (tm_pred (tm_var n)))))
              (tm_abs n ty_Nat
                (tm_if0 (tm_var n)
                  (tm_nat 0)
                  (tm_app (tm_fst (tm_var eo)) (tm_pred (tm_var n))))))))
      (tm_let even (tm_fst (tm_var evenodd))
      (tm_let odd (tm_snd (tm_var evenodd))
      (tm_pair
        (tm_app (tm_var even) (tm_nat 3))
        (tm_app (tm_var even) (tm_nat 4))))).


    (*
    Example eotest_typechecks :
      has_type (@empty ty) eotest (ty_prod ty_Nat ty_Nat).
    Proof. unfold eotest. eauto 30.
    Qed.
    *)

    (*
    Example eotest_example1:
      eotest ==>* (tm_pair (tm_nat 0) (tm_nat 1)).
    Proof. unfold eotest. normalize. Qed.
    *)

    End FixTest4.

    End Examples.

型付けの性質
~~~~~~~~~~~~

このシステムの進行と保存の証明は、純粋な単純型付きラムダ計算のものと本質的に同じです(もちろんいくらか長くはなりますが)。

進行
^^^^

::

    Theorem progress : forall t T,
         has_type empty t T ->
         value t \/ exists t', t ==> t'.
    Proof with eauto.


      (* 定理: empty |- t : T と仮定する。すると次のいずれかである:
           1. t は値、または
           2. ある t' について t ==> t' 
         証明: 与えられた型導出についての帰納法によって。 *)

    intros t T Ht.
      remember (@empty ty) as Gamma.
      generalize dependent HeqGamma.
      has_type_cases (induction Ht) Case; intros HeqGamma; subst.
      Case "T_Var".


        (* 与えられた型導出の最後の規則が [T_Var] ではあり得ない。
           なぜなら、この規則では [empty |- x : T] にならないので
           (コンテキストが empty ではない)。*)

    inversion H.
      Case "T_Abs".


        (* もし [T_Abs] が最後の規則ならば、[t = tm_abs x T11 t12] となるが、
           これは値である。 *)

    left...
      Case "T_App".


        (* 最後の規則が T_App ならば、[t = t1 t2] である。規則の形から
             [empty |- t1 : T1 -> T2]
             [empty |- t2 : T1]
           となる。帰納法の仮定から、t1 と t2 のそれぞれは値であるかステップを進むことができる。 *)

    right.
        destruct IHHt1; subst...
        SCase "t1 is a value".
          destruct IHHt2; subst...
          SSCase "t2 is a value".


          (* [t1] と [t2] がどちらも値のとき、[t1 = tm_abs x T11 t12] となる。
             なぜなら関数抽象は、関数型を持つ唯一の値であるから。しかし、[ST_AppAbs]より
             [(tm_abs x T11 t12) t2 ==> subst x t2 t12] となる。 *)

    inversion H; subst; try (solve by inversion).
            exists (subst x t2 t12)...
          SSCase "t2 steps".


            (* もし [t1] が値で [t2 ==> t2'] ならば、
               [ST_App2]より [t1 t2 ==> t1 t2'] である。 *)

    destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
        SCase "t1 steps".


          (* 最後に、もし [t1 ==> t1'] ならば、
             [ST_App1] より [t1 t2 ==> t1' t2] である。 *)

    destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    Qed.

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
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    .

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
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    Qed.

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
        apply not_eq_beq_id_false in H2. rewrite H2 in Hctx...
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    Qed.

保存
^^^^

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S  ->
         has_type empty v U   ->
         has_type Gamma (subst x v t) S.
    Proof with eauto.


      (* 定理: もし Gamma,x:U |- t : S かつ empty |- v : U ならば、
         Gamma |- (subst x v t) S. である。 *)

    intros Gamma x U v t S Htypt Htypv.
      generalize dependent Gamma. generalize dependent S.


      (* 証明: t についての帰納法を使う。ほとんどの場合は、帰納仮定から直接示される。
         tm_var と tm_abs だけが例外である。
         前者は自動化できない。変数がどのように相互作用するか推論しなければならないからである。 *)

    tm_cases (induction t) Case;
        intros S Gamma Htypt; simpl; inversion Htypt; subst...
      Case "tm_var".
        simpl. rename i into y.


        (* もし t = y ならば、次が成立する:
             [empty |- v : U] and
             [Gamma,x:U |- y : S]
           そして、inversion から [extend Gamma x U y = Some S] となる。
           示したいのは [Gamma |- subst x v y : S] である。

           考慮するのは2つの場合、[x=y] の場合と [x<>y] の場合である。 *)

    remember (beq_id x y) as e. destruct e.
        SCase "x=y".


        (* もし [x = y] ならば、[U = S] であり、また [subst x v y = v] である。
           これから実際に示さなければならないことは、
           もし [empty |- v : U] ならば [Gamma |- v : U] である、ということである。
           この定理のより一般化されたバージョンを既に証明している。それはコンテキスト不変性である。 *)

    apply beq_id_eq in Heqe. subst.
          unfold extend in H1. rewrite <- beq_id_refl in H1.
          inversion H1; subst. clear H1.
          eapply context_invariance...
          intros x Hcontra.
          destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
          inversion HT'.
        SCase "x<>y".


        (* もし [x <> y] ならば、[Gamma y = Some S] で、置換は何も影響しない。
           [T_Var] より [Gamma |- y : S] を示すことができる。 *)

    apply T_Var... unfold extend in H1. rewrite <- Heqe in H1...
      Case "tm_abs".
        rename i into y. rename t into T11.


        (* もし [t = tm_abs y T11 t0] ならば、次が成立する:
             [Gamma,x:U |- tm_abs y T11 t0 : T11->T12]
             [Gamma,x:U,y:T11 |- t0 : T12]
             [empty |- v : U]
           帰納仮定より、すべての S Gamma について
             [Gamma,x:U |- t0 : S -> Gamma |- subst x v t0 S] となる。

           次の計算ができる:
             subst x v t = tm_abs y T11 (if beq_id x y
                                          then t0
                                          else subst x v t0)
           そして、示すべきことは [Gamma |- subst x v t : T11->T12] である。
           [T_Abs] を使うためには、残っているのは次を示すことである:
             [Gamma,y:T11 |- if beq_id x y then t0 else subst x v t0 : T12]
           2つの場合、[x = y] の場合と [x <> y] の場合を考える。
        *)

    apply T_Abs...
        remember (beq_id x y) as e. destruct e.
        SCase "x=y".


        (* もし [x = y] ならば、置換は何も影響しない。
           コンテキスト不変性より [Gamma,y:U,y:T11] と [Gamma,y:T11] 
           が同値であることが示される。前者のコンテキストが [t0 : T12] を示すことから、
           後者についても同じことが言える。 *)

    eapply context_invariance...
          apply beq_id_eq in Heqe. subst.
          intros x Hafi. unfold extend.
          destruct (beq_id y x)...
        SCase "x<>y".


        (* もし [x <> y] ならば、帰納仮定とコンテキスト不変性より次が示される:
             [Gamma,x:U,y:T11 |- t0 : T12]       =>
             [Gamma,y:T11,x:U |- t0 : T12]       =>
             [Gamma,y:T11 |- subst x v t0 : T12] *)

    apply IHt. eapply context_invariance...
          intros z Hafi. unfold extend.
          remember (beq_id y z) as e0. destruct e0...
          apply beq_id_eq in Heqe0. subst.
          rewrite <- Heqe...
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    Qed.

    Theorem preservation : forall t t' T,
         has_type empty t T  ->
         t ==> t'  ->
         has_type empty t' T.
    Proof with eauto.
      intros t t' T HT.


      (* 定理: もし [empty |- t : T] かつ [t ==> t'] ならば、[empty |- t' : T] である。 *)

    remember (@empty ty) as Gamma. generalize dependent HeqGamma.
      generalize dependent t'.


      (* 証明: 与えられた型導出についての帰納法を使う。ほとんどの場合は、
         [T_Var] と [T_Abs] の矛盾である(contradictory ([T_Var], [T_Abs]))。
         興味深いものだけを示す。 *)

    has_type_cases (induction HT) Case;
        intros t' HeqGamma HE; subst; inversion HE; subst...
      Case "T_App".


        (* もし最後の規則が [T_App] ならば、[t = t1 t2] である。
           [t ==> t'] を示すのに使うことができる規則は3つ、[ST_App1]、[ST_App2]、[ST_AppAbs]
           である。最初の2つについては、結果は帰納仮定から直ぐに導かれる。 *)

    inversion HE; subst...
        SCase "ST_AppAbs".


          (* 3つ目の場合、
               [t1 = tm_abs x T11 t12]
             かつ
               [t2 = v2]
             と仮定する。示すべきは [empty |- subst x v2 t12 : T2] である。
             仮定から
                 [empty |- tm_abs x T11 t12 : T1->T2]
             であり、inversion から
                 [x:T1 |- t12 : T2]
             となる。
             substitution_preserves_typing を既に証明しており、また仮定から
                 [empty |- v2 : T1]
             である。これで証明された。 *)

    apply substitution_preserves_typing with T1...
          inversion HT1...
      (* FILL IN HERE *)


      (* ここを埋めなさい *)

    Qed.

☐

::

    End STLCExtended.

