Subtyping\_J :サブタイプ
========================

概念
----

さて、サブタイプ(*subtyping*)の学習に入ります。サブタイプはおそらく、近年設計されたプログラミング言語で使われる静的型システムの最も特徴的な機能です。

動機付けのための例
~~~~~~~~~~~~~~~~~~

レコードを持つ単純型付きラムダ計算では、項

::

        (\r:{y:Nat}. (r.y)+1) {x=10,y=11}

は型付けできません。なぜなら、これはフィールドが1つのレコードを引数としてとる関数に2つのフィールドを持つレコードが与えられている部分を含んでいて、一方、\ ``T_App``\ 規則は関数の定義域の型は引数の型に完全に一致することを要求するからです。

しかしこれは馬鹿らしいことです。実際には関数に、必要とされるものより良い引数を与えているのです!この関数の本体がレコード引数\ ``r``\ に対して行うことができることはおそらく、そのフィールド\ ``y``\ を射影することだけです。型から許されることは他にはありません。すると、他に\ ``x``\ フィールドが存在するか否かは何の違いもないはずです。これから、直観的に、この関数は少なくとも\ ``y``\ フィールドは持つ任意のレコード値に適用可能であるべきと思われます。

同じことを別の観点から見ると、より豊かなフィールドを持つレコードは、そのサブセットのフィールドだけを持つレコードと「任意のコンテキストで少なくとも同等の良さである」と言えるでしょう。より長い(多いフィールドを持つ)レコード型の任意の値は、より短かいレコード型が求められるコンテキストで「安全に」(*safely*)使えるという意味においてです。コンテキストがより短かい型のものを求めているときに、より長い型のものを与えた場合、何も悪いことは起こらないでしょう(形式的には、プログラムは行き詰まることはないでしょう)。

ここではたらいている一般原理はサブタイプ(付け)(*subtyping*)と呼ばれます。型\ ``T``\ の値が求められている任意のコンテキストで型\ ``S``\ の値が安全に使えるとき、「\ ``S``\ は\ ``T``\ のサブタイプである」と言い、非形式的に\ ``S <: T``\ と書きます。サブタイプの概念はレコードだけではなく、関数、対、など言語のすべての型コンストラクタに適用されます。

サブタイプとオブジェクト指向言語
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

サブタイプは多くのプログラミング言語で重要な役割を演じます。特に、オブジェクト指向言語のサブクラス(*subclassing*)の概念と近い関係にあります。

(JavaやC\ ``#``\ 等の)オブジェクトはレコードと考えることができます。いくつかのフィールドは関数(「メソッド」)で、いくつかのフィールドはデータ値(「フィールド」または「インスタンス変数」)です。オブジェクト\ ``o``\ のメソッド\ ``m``\ を引数\ ``a1..an``\ のもとで呼ぶことは、\ ``o``\ から\ ``m``\ フィールドを射影として抽出して、それを\ ``a1..an``\ に適用することです。

オブジェクトの型はクラス(*class*)またはインターフェース(*interface*)として与えることができます。この両者はどちらも、どのメソッドとどのデータフィールドをオブジェクトが提供するかを記述します。

クラスやインターフェースは、サブクラス(*subclass*)関係やサブインターフェース(*subinterface*)関係で関係づけられます。サブクラス(またはサブインターフェース)に属するオブジェクトには、スーパークラス(またはスーパーインターフェース)に属するオブジェクトのメソッドとフィールドのすべての提供することが求められ、おそらくそれに加えてさらにいくつかのものを提供します。

サブクラス(またはサブインターフェース)のオブジェクトをスーパークラス(またはスーパーインターフェース)のオブジェクトの場所で使えるという事実は、複雑なライブラリの構築にきわめて便利なほどの柔軟性を提供します。例えば、Javaの
Swingフレームワークのようなグラフィカルユーザーインターフェースツールキットは、スクリーンに表示できユーザとインタラクションできるグラフィカルな表現を持つすべてのオブジェクトに共通のフィールドとメソッドを集めた、抽象インターフェース\ ``Component``\ を定義するでしょう。そのようなオブジェクトの例としては、典型的なGUIのボタン、チェックボックス、スクロールバーなどがあります。この共通インターフェースのみに依存するメソッドは任意のそれらのオブジェクトに適用できます。

もちろん、実際のオブジェクト指向言語はこれらに加えてたくさんの他の機能を持っています。フィールドは更新できます。フィールドとメソッドは\ ``private``\ と宣言できます。クラスはまた、オブジェクトを構成しそのメソッドをインプリメントするのに使われる「コード」を与えます。そしてサブクラスのコードは「継承」を通じてスーパークラスのコードと協調します。クラスは、静的なメソッドやフィールド、イニシャライザ、等々を持つことができます。

ものごとを単純なまま進めるために、これらの問題を扱うことはしません。実際、これ以上オブジェクトやクラスについて話すことはありません。(もし興味があるなら、
Types and Programming Languages
にたくさんの議論があります。)その代わり、STLCの単純化された設定のもとで、サブクラス/サブインターフェース関係の背後にある核となる概念について学習します。

包摂規則
~~~~~~~~

この章のゴールは(直積を持つ)単純型付きラムダ計算にサブタイプを追加することです。これは2つのステップから成ります:

-  型の間の二項サブタイプ関係(*subtype relation*)を定義します。
-  型付け関係をサブタイプを考慮した形に拡張します。

2つ目のステップは実際はとても単純です。型付け関係にただ1つの規則だけを追加します。その規則は、包摂規則(*rule
of subsumption*)と呼ばれます:

::

                             Gamma |- t : S     S <: T
                             -------------------------                      (T_Sub)
                                   Gamma |- t : T

この規則は、直観的には、項について知っている情報のいくらかを「忘れる」ことができると言っています。

例えば、\ ``t``\ が2つのフィールドを持つレコード(例えば、\ ``S = {x:A->A, y:B->B}``)で、フィールドの1つを忘れることにした(``T = {y:B->B}``)とします。すると\ ``t``\ を、1フィールドのレコードを引数としてとる関数に渡すことができるようになります。

サブタイプ関係
~~~~~~~~~~~~~~

最初のステップ、関係\ ``S <: T``\ の定義にすべてのアクションがあります。定義のそれぞれを見てみましょう。

直積型
^^^^^^

最初に、直積型です。ある一つの対が他の対より「良い」とは、それぞれの成分が他の対の対応するものより良いことです。

::

                                S1 <: T1    S2 <: T2
                                --------------------                        (S_Prod)
                                   S1*S2 <: T1*T2

関数型
^^^^^^

次の型を持つ2つの関数\ ``f``\ と\ ``g``\ があるとします：

::

           f : C -> {x:A,y:B}
           g : (C->{y:B}) -> D

つまり、\ ``f``\ は型\ ``{x:A,y:B}``\ のレコードを引数とする関数であり、\ ``g``\ は引数として、型\ ``{y:B}``\ のレコードを引数とする関数をとる高階関数です。(そして、レコードのサブタイプについてはまだ議論していませんが、\ ``{x:A,y:B}``\ は\ ``{y:B}``\ のサブタイプであるとします。)すると、関数適用\ ``g f``\ は、両者の型が正確に一致しないにもかかわらず安全です。なぜなら、\ ``g``\ が\ ``f``\ について行うことができるのは、\ ``f``\ を(型\ ``C``\ の)ある引数に適用することだけだからです。その結果は実際には2フィールドのレコードになります。ここで\ ``g``\ が期待するのは1つのフィールドを持つレコードだけです。しかしこれは安全です。なぜなら\ ``g``\ がすることができるのは、わかっている1つのフィールドを射影することだけで、それは存在する2つのフィールドの1つだからです。

この例から、関数型のサブタイプ規則が以下のようになるべきということが導かれます。2つの関数型がサブタイプ関係にあるのは、その結果が次の条件のときです:

::

                                      S2 <: T2
                                  ----------------                        (S_Arrow2)
                                  S1->S2 <: S1->T2

これを一般化して、2つの関数型のサブタイプ関係を、引数の条件を含めた形にすることが、同様にできます:

::

                                T1 <: S1    S2 <: T2
                                --------------------                      (S_Arrow)
                                  S1->S2 <: T1->T2

ここで注意するのは、引数の型はサブタイプ関係が逆向きになることです。\ ``S1->S2``\ が\ ``T1->T2``\ のサブタイプであると結論するためには、\ ``T1``\ が\ ``S1``\ のサブタイプでなければなりません。関数型のコンストラクタは最初の引数について反変(*contravariant*)であり、二番目の引数について共変(*covariant*)であると言います。

直観的には、型\ ``S1->S2``\ の関数\ ``f``\ があるとき、\ ``f``\ は型\ ``S1``\ の要素を引数にとることがわかります。明らかに\ ``f``\ は\ ``S1``\ の任意のサブタイプ\ ``T1``\ の要素をとることもできます。\ ``f``\ の型は同時に\ ``f``\ が型\ ``S2``\ の要素を返すことも示しています。この値が\ ``S2``\ の任意のスーパータイプ\ ``T2``\ に属することも見ることができます。つまり、型\ ``S1->S2``\ の任意の関数\ ``f``\ は、型\ ``T1->T2``\ を持つと見ることもできるということです。

Top
^^^

サブタイプ関係の最大要素を定めることは自然です。他のすべての型のスーパータイプであり、すべての(型付けできる)値が属する型です。このために言語に新しい一つの型定数\ ``Top``\ を追加し、\ ``Top``\ をサブタイプ関係の他のすべての型のスーパータイプとするサブタイプ規則を定めます:

::

                                       --------                             (S_Top)
                                       S <: Top

``Top``\ 型はJavaやC\ ``#``\ における\ ``Object``\ 型に対応するものです。

構造規則
^^^^^^^^

サブタイプ関係の最後に、2つの「構造規則」("structural
rules")を追加します。これらは特定の型コンストラクタからは独立したものです。推移律(rule
of
*transitivity*)は、直観的には、\ ``S``\ が\ ``U``\ よりも良く、\ ``U``\ が\ ``T``\ よりも良ければ、\ ``S``\ は\ ``T``\ よりも良いというものです...

::

                                  S <: U    U <: T
                                  ----------------                        (S_Trans)
                                       S <: T

... そして反射律(rule of
*reflexivity*)は、任意の型はそれ自身と同じ良さを持つというものです。

::

                                       ------                              (S_Refl)
                                       T <: T

レコード
^^^^^^^^

レコード型のサブタイプは何でしょうか？

レコード型のサブタイプについての基本的直観は、「より小さな」レコードの場所で「より大きな」レコードを使うことは常に安全だということです。つまり、レコード型があるとき、さらにフィールドを追加したものは常にサブタイプになるということです。もしあるコードがフィールド\ ``x``\ と\ ``y``\ を持つレコードを期待していたとき、レコード\ ``x``\ 、\ ``y``\ 、\ ``z``\ を持つレコードを受けとることは完璧に安全です。\ ``z``\ フィールドは単に無視されるだけでしょう。例えば次の通りです。

::

           {x:Nat,y:Bool} <: {x:Nat}
           {x:Nat} <: {}

これはレコードの"width subtyping"(幅サブタイプ)として知られます。

レコードの1つのフィールドの型をそのサブタイプで置き換えることでも、レコードのサブタイプを作ることができます。もしあるコードが型\ ``T``\ のフィールド\ ``x``\ を持つレコードを待っていたとき、型\ ``S``\ が型\ ``T``\ のサブタイプである限りは、型\ ``S``\ のフィールド\ ``x``\ を持つレコードが来ることはハッピーです。例えば次の通りです。

::

           {a:{x:Nat}} <: {a:{}}

これは"depth subtyping"(深さサブタイプ)として知られています。

最後に、レコードのフィールドは特定の順番で記述されますが、その順番は実際には問題ではありません。例えば次の通りです。

::

           {x:Nat,y:Bool} <: {y:Bool,x:Nat}

これは"permutation subtyping"(順列サブタイプ)として知られています。

これらをレコードについての単一のサブタイプ規則に形式化することをやってみましょう。次の通りです:

::

                            for each jk in j1..jn,
                        exists ip in i1..im, such that
                              jk=ip and Sp <: Tk
                      ----------------------------------                    (S_Rcd)
                      {i1:S1...im:Sm} <: {j1:T1...jn:Tn}

つまり、左のレコードは(少なくとも)右のレコードのフィールドラベルをすべて持ち、両者で共通するフィールドはサブタイプ関係になければならない、ということです。しかしながら、この規則はかなり重くて読むのがたいへんです。ここでは、3つのより簡単な規則に分解します。この3つは\ ``S_Trans``\ を使うことで結合することができ、同じ作用をすることができます。

最初に、レコード型の最後にフィールドを追加したものはサブタイプになります:

::

                                   n > m
                     ---------------------------------                 (S_RcdWidth)
                     {i1:T1...in:Tn} <: {i1:T1...im:Tm}

``S_RcdWidth``\ を使うと、複数のフィールドを持つレコードについて、前方のフィールドを残したまま後方のフィールドを落とすことができます。この規則で例えば\ ``{y:B, x:A} <: {y:B}``\ が示されます。

二つ目に、レコード型の構成要素の内部にサブタイプ規則を適用できます:

::

                           S1 <: T1  ...  Sn <: Tn
                      ----------------------------------               (S_RcdDepth)
                      {i1:S1...in:Sn} <: {i1:T1...in:Tn}

例えば\ ``S_RcdDepth``\ と\ ``S_RcdWidth``\ を両方使って\ ``{y:{z:B}, x:A} <: {y:{}}``\ を示すことができます。

三つ目に、フィールドの並べ替えを可能にする必要があります。念頭に置いてきた例は\ ``{x:A,y:B} <: {y:B}``\ でした。これはまだ達成されていませんでした。\ ``S_RcdDepth``\ と\ ``S_RcdWidth``\ だけでは、レコード型の「後」からフィールドを落とすことしかできません。これから次の規則が必要です:

::

             {i1:S1...in:Sn} is a permutation of {i1:T1...in:Tn}
             ---------------------------------------------------        (S_RcdPerm)
                      {i1:S1...in:Sn} <: {i1:T1...in:Tn}

さらなる例です:

-  ``{x:A,y:B}``\ <:``{y:B,x:A}``.
-  ``{}->{j:A} <: {k:B}->Top``
-  ``Top->{k:A,j:B} <: C->{j:B}``

なお、実際の言語ではこれらのサブタイプ規則のすべてを採用しているとは限らないことは、注記しておくべきでしょう。例えばJavaでは:

-  サブクラスではスーパークラスのメソッドの引数または結果の型を変えることはできません
   (つまり、depth
   subtypingまたは関数型サブタイプのいずれかができないということです。どちらかは見方によります)。
-  それぞれのクラスは(直上の)スーパークラスを1つだけ持ちます(クラスの「単一継承」
   ("single inheritance")です)。

-  各クラスのメンバー(フィールドまたはメソッド)は1つだけインデックスを持ち、
   サブクラスでメンバーが追加されるたびに新しいインデックスが「右に」追加されます(つまり、クラスには並び換えがありません)。
-  クラスは複数のインターフェースをインプリメントできます。これは
   インターフェースの「多重継承」("multiple
   inheritance")と呼ばれます(つまり、インターフェースには並び換えがあります)。

直積と Top によるレコード (optional)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

これらすべてをどのように形式化するかは、レコードとその型をどのように形式化するかに、まさに依存しています。もしこれらを核言語の一部として扱うならば、そのためのサブタイプ規則を書き下す必要があります。ファイル\ ``RecordSub_J.v``\ で、この拡張がどのようにはたらくかを示します。

一方、もしそれらをパーサで展開される派生形として扱うならば、新しい規則は何も必要ありません。直積と\ ``Unit``\ 型のサブタイプについての既存の規則が、このエンコードによるレコードのサブタイプに関する妥当な規則になっているかをチェックすれば良いだけです。このために、前述のエンコードをわずかに変更する必要があります。組のエンコードのベースケースおよびレコードのエンコードの
"don't care"
プレースホルダとして、\ ``Unit``\ の代わりに\ ``Top``\ を使います。すると:

::

        {a:Nat, b:Nat} ----> {Nat,Nat}       つまり (Nat,(Nat,Top))
        {c:Nat, a:Nat} ----> {Nat,Top,Nat}   つまり (Nat,(Top,(Nat,Top)))

レコード値のエンコードは何も変更しません。このエンコードで上述のサブタイプ規則が成立することをチェックするのは容易です(そしてタメになります)。この章の残りでは、このアプローチを追求します。

中核部の定義
------------

STLCに必要となる重要な拡張を既に概観してきました:(1)サブタイプ関係を追加し、(2)型関係に包摂規則を拡張することです。すべてがスムースにいくように、前の章の表現にいくらかの技術的改善を行います。定義の残りは
-- 特に言語の構文と操作的意味は --
前の章で見たものと同じです。最初に同じ部分をやってみましょう。

構文
^^^^

よりおもしろい例のために、純粋STLCに非常に小さな拡張を行います。\ ``String``\ 、\ ``Person``\ 、\ ``Window``\ 等のような、任意の「基本型」の集合を追加します。これらの型の定数を追加したり、その型の上の操作を追加したりすることをわざわざやりませんが、そうすることは簡単です。

この章の残りでは、基本型、ブール型、関数型、\ ``Unit``\ と\ ``Top``\ のみ形式化し、直積型は練習問題にします。

::

    Inductive ty : Type :=
      | ty_Top   : ty
      | ty_Bool  : ty
      | ty_base  : id -> ty
      | ty_arrow : ty -> ty -> ty
      | ty_Unit  : ty
    .

    Tactic Notation "ty_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ty_Top" | Case_aux c "ty_Bool"
      | Case_aux c "ty_base" | Case_aux c "ty_arrow"
      | Case_aux c "ty_Unit" |
      ].

    Inductive tm : Type :=
      | tm_var : id -> tm
      | tm_app : tm -> tm -> tm
      | tm_abs : id -> ty -> tm -> tm
      | tm_true : tm
      | tm_false : tm
      | tm_if : tm -> tm -> tm -> tm
      | tm_unit : tm
    .

    Tactic Notation "tm_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "tm_var" | Case_aux c "tm_app"
      | Case_aux c "tm_abs" | Case_aux c "tm_true"
      | Case_aux c "tm_false" | Case_aux c "tm_if"
      | Case_aux c "tm_unit"
      ].

包摂
^^^^

包摂の定義は、いつものSTLCと同様です。

::

    Fixpoint subst (s:tm) (x:id) (t:tm) : tm :=
      match t with
      | tm_var y =>
          if beq_id x y then s else t
      | tm_abs y T t1 =>
          tm_abs y T (if beq_id x y then t1 else (subst s x t1))
      | tm_app t1 t2 =>
          tm_app (subst s x t1) (subst s x t2)
      | tm_true =>
          tm_true
      | tm_false =>
          tm_false
      | tm_if t1 t2 t3 =>
          tm_if (subst s x t1) (subst s x t2) (subst s x t3)
      | tm_unit =>
          tm_unit
      end.

簡約
^^^^

``value``\ (値)の定義や\ ``step``\ 関係の定義と同様です。

::

    Inductive value : tm -> Prop :=
      | v_abs : forall x T t,
          value (tm_abs x T t)
      | t_true :
          value tm_true
      | t_false :
          value tm_false
      | v_unit :
          value tm_unit
    .

    Hint Constructors value.

    Reserved Notation "t1 '==>' t2" (at level 40).

    Inductive step : tm -> tm -> Prop :=
      | ST_AppAbs : forall x T t12 v2,
             value v2 ->
             (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
      | ST_App1 : forall t1 t1' t2,
             t1 ==> t1' ->
             (tm_app t1 t2) ==> (tm_app t1' t2)
      | ST_App2 : forall v1 t2 t2',
             value v1 ->
             t2 ==> t2' ->
             (tm_app v1 t2) ==> (tm_app v1  t2')
      | ST_IfTrue : forall t1 t2,
          (tm_if tm_true t1 t2) ==> t1
      | ST_IfFalse : forall t1 t2,
          (tm_if tm_false t1 t2) ==> t2
      | ST_If : forall t1 t1' t2 t3,
          t1 ==> t1' ->
          (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
    where "t1 '==>' t2" := (step t1 t2).

    Tactic Notation "step_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
      | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue"
      | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
      ].

    Hint Constructors step.

サブタイプ
----------

さて、おもしろい所にやって来ました。サブタイプ関係の定義から始め、その重要な技術的性質を調べます。

定義
~~~~

サブタイプの定義は、動機付けの議論のところで概観した通りです。

::

    Inductive subtype : ty -> ty -> Prop :=
      | S_Refl : forall T,
        subtype T T
      | S_Trans : forall S U T,
        subtype S U ->
        subtype U T ->
        subtype S T
      | S_Top : forall S,
        subtype S ty_Top
      | S_Arrow : forall S1 S2 T1 T2,
        subtype T1 S1 ->
        subtype S2 T2 ->
        subtype (ty_arrow S1 S2) (ty_arrow T1 T2)
    .

なお、基本型については特別な規則は何ら必要ありません。基本型は自動的に(``S_Refl``\ より)自分自身のサブタイプであり、(``S_Top``\ より)\ ``Top``\ のサブタイプでもあります。そしてこれが必要な全てです。

::

    Hint Constructors subtype.

    Tactic Notation "subtype_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "S_Refl" | Case_aux c "S_Trans"
      | Case_aux c "S_Top" | Case_aux c "S_Arrow"
      ].

サブタイプの例と練習問題
~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module Examples.

    Notation x := (Id 0).
    Notation y := (Id 1).
    Notation z := (Id 2).

    Notation A := (ty_base (Id 6)).
    Notation B := (ty_base (Id 7)).
    Notation C := (ty_base (Id 8)).

    Notation String := (ty_base (Id 9)).
    Notation Float := (ty_base (Id 10)).
    Notation Integer := (ty_base (Id 11)).

練習問題: ★★, optional (subtyping judgements)
'''''''''''''''''''''''''''''''''''''''''''''

(この練習問題は、少なくともファイルのここまでに、直積型を言語に追加した後で行ってください。)

レコードを対でエンコードするときに、以下のレコード型を表す直積型を定義しなさい。

::

        Person   := { name : String }
        Student  := { name : String ;
                      gpa  : Float }
        Employee := { name : String ;
                      ssn  : Integer }

    Definition Person : ty :=
     Admitted.

☐

::

    Example subtyping_example_0 :
      subtype (ty_arrow C Person)
              (ty_arrow C ty_Top).

以下の事実のほとんどは、Coqで証明するのは簡単です。練習問題の効果を十分に得るために、どうやって証明するか自分が理解していることを紙に証明を書いて確認しなさい。

練習問題: ★, optional (subtyping\_example\_1)
'''''''''''''''''''''''''''''''''''''''''''''

::

    Example subtyping_example_1 :
      subtype (ty_arrow ty_Top Student)
              (ty_arrow (ty_arrow C C) Person).
     Admitted.

☐

練習問題: ★, optional (subtyping\_example\_2)
'''''''''''''''''''''''''''''''''''''''''''''

::

    Example subtyping_example_2 :
      subtype (ty_arrow ty_Top Person)
              (ty_arrow Person ty_Top).
     Admitted.

☐

::

    End Examples.

練習問題: ★, optional (subtype\_instances\_tf\_1)
'''''''''''''''''''''''''''''''''''''''''''''''''

型\ ``S``\ 、\ ``T``\ 、\ ``U``\ 、\ ``V``\ があり\ ``S <: T``\ かつ\ ``U <: V``\ とします。このとき以下のサブタイプ関係の主張のうち、正しいものはどれでしょうか？それぞれの後に「真」または「偽」と書きなさい。(ここで、\ ``A``\ 、\ ``B``\ 、\ ``C``\ は基本型とします。)

-  ``T->S <: T->S``
-  ``Top->U <: S->Top``
-  ``(C->C) -> (A*B)  <:  (C->C) -> (Top*B)``
-  ``T->T->U <: S->S->V``
-  ``(T->T)->U <: (S->S)->V``
-  ``((T->S)->T)->U <: ((S->T)->S)->V``
-  ``S*V <: T*U``

☐

練習問題: ★ (subtype\_instances\_tf\_2)
'''''''''''''''''''''''''''''''''''''''

以下の主張のうち正しいものはどれでしょうか？それぞれについて「真」または「偽」と書きなさい。

::

          forall S T,
              S <: T  ->
              S->S   <:  T->T

          forall S T,
               S <: A->A ->
               exists T,
                  S = T->T  /\  T <: A

          forall S T1 T1,
               S <: T1 -> T2 ->
               exists S1 S2,
                  S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2

          exists S,
               S <: S->S

          exists S,
               S->S <: S

          forall S T2 T2,
               S <: T1*T2 ->
               exists S1 S2,
                  S = S1*S2  /\  S1 <: T1  /\  S2 <: T2

☐

練習問題: ★ (subtype\_concepts\_tf)
'''''''''''''''''''''''''''''''''''

以下のうち真であるものはどれで、偽であるものはどれでしょうか？

-  他のすべての型のスーパータイプである型がある。
-  他のすべての型のサブタイプである型がある。
-  他のすべての対型のスーパータイプである対型がある。
-  他のすべての対型のサブタイプである対型がある。
-  他のすべての関数型のスーパータイプである関数型がある。
-  他のすべての関数型のサブタイプである関数型がある。
-  サブタイプ関係による、同一型を含まない無限降鎖(infinite descending
   chain)がある。 つまり型の無限列\ ``S0``\ 、\ ``S1``\ 、...
   があり、すべての\ ``Si``\ は異なり、そして各\ ``S(i+1)``\ は\ ``S(i)``\ のサブタイプである。
-  サブタイプ関係による、同一型を含まない無限昇鎖(infinite *ascending*
   chain)がある。 つまり型の無限列\ ``S0``\ 、\ ``S1``\ 、...
   があり、すべての\ ``Si``\ は異なり、そして各\ ``S(i+1)``\ は\ ``S(i)``\ のスーパータイプである。

☐

練習問題: ★★ (proper\_subtypes)
'''''''''''''''''''''''''''''''

次の主張は真でしょうか偽でしょうか？自分の答えを簡単に説明しなさい。

::

        forall T,
             ~(exists n, T = ty_base n) ->
             exists S,
                S <: T  /\  S <> T

☐

練習問題: ★★ (small\_large\_1)
''''''''''''''''''''''''''''''

-  次の表明を真にする最小の型\ ``T``\ は何でしょうか？
   (ここで「最小」とはサブタイプ関係においてです。)

   ::

          empty |- (\p:T*Top. p.fst) ((\z:A.z), unit) : A->A

-  同じ表明を真にする最大の型\ ``T``\ は何でしょうか？

☐

練習問題: ★★ (small\_large\_2)
''''''''''''''''''''''''''''''

-  次の表明を真にする最小の型\ ``T``\ は何でしょうか？

   ::

          empty |- (\p:(A->A * B->B). p) ((\z:A.z), (\z:B.z)) : T

-  同じ表明を真にする最大の型\ ``T``\ は何でしょうか？

☐

練習問題: ★★, optional (small\_large\_3)
''''''''''''''''''''''''''''''''''''''''

-  次の表明を真にする最小の型\ ``T``\ は何でしょうか？

   ::

          a:A |- (\p:(A*T). (p.snd) (p.fst)) (a , \z:A.z) : A

-  同じ表明を真にする最大の型\ ``T``\ は何でしょうか？

☐

練習問題: ★★ (small\_large\_4)
''''''''''''''''''''''''''''''

-  次の表明を真にする最小の型\ ``T``\ は何でしょうか？

   ::

          exists S,
            empty |- (\p:(A*T). (p.snd) (p.fst)) : S

-  同じ表明を真にする最大の型\ ``T``\ は何でしょうか？

☐

練習問題: ★★ (smallest\_1)
''''''''''''''''''''''''''

次の表明を真にする最小の型\ ``T``\ は何でしょうか？

::

          exists S, exists t,
            empty |- (\x:T. x x) t : S

☐

練習問題: ★★ (smallest\_2)
''''''''''''''''''''''''''

次の表明を真にする最小の型\ ``T``\ は何でしょうか？

::

          empty |- (\x:Top. x) ((\z:A.z) , (\z:B.z)) : T

☐

練習問題: ★★★, optional (count\_supertypes)
'''''''''''''''''''''''''''''''''''''''''''

レコード型\ ``{x:A, y:C->C}``\ はいくつのスーパータイプを持つでしょうか？つまり、いくつの異なる型\ ``T``\ が\ ``{x:A, y:C->C} <: T``\ を満たすでしょうか?(ここで、2つの型が異なるとは、その記述が異なることとします。たとえ両者が相互にサブタイプであってもです。例えば、\ ``{x:A,y:B}``\ と\ ``{y:B,x:A}``\ は異なります。)

☐

型付け
------

型付け関係の変更は、包摂規則\ ``T_Sub``\ の追加だけです。

::

    Definition context := id -> (option ty).
    Definition empty : context := (fun _ => None).
    Definition extend (Gamma : context) (x:id) (T : ty) :=
      fun x' => if beq_id x x' then Some T else Gamma x'.

    Inductive has_type : context -> tm -> ty -> Prop :=

型付けの例
~~~~~~~~~~

::

    Module Examples2.
    Import Examples.

以下の練習問題は言語に直積を追加した後に行いなさい。それぞれの非形式的な型付けジャッジメントについて、Coqで形式的主張を記述し、それを証明しなさい。

練習問題: ★, optional (typing\_example\_0)
''''''''''''''''''''''''''''''''''''''''''

☐

練習問題: ★★, optional (typing\_example\_1)
'''''''''''''''''''''''''''''''''''''''''''

☐

練習問題: ★★, optional (typing\_example\_2)
'''''''''''''''''''''''''''''''''''''''''''

☐

::

    End Examples2.

性質
----

チェックしたいシステムの根本的性質はいつもと同じく、進行と保存です。STLCに参照を拡張したものとは違い、サブタイプを考慮しても、これらの主張を変化させる必要はありません。ただし、それらの証明はもうちょっと複雑になります。

サブタイプの反転補題(Inversion Lemmas)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

型付け関係の性質を見る前に、サブタイプ関係の2つの重要な構造的性質を記しておかなければなりません:

-  ``Bool``\ は\ ``Bool``\ の唯一のサブタイプです
-  関数型のすべてのサブタイプは関数型です

これらは反転補題(*inversion
lemmas*)と呼ばれます。これは、後の証明でもともとの\ ``inversion``\ タクティックと同じ役目をするためです。つまり、サブタイプ関係の主張\ ``S <: T``\ の導出が存在するという仮定と、\ ``S``\ や\ ``T``\ の形についてのいくつかの制約が与えられたとき、それぞれの補題は、\ ``S``\ と\ ``T``\ の形、および両者の構成要素間のサブタイプ関係の存在について、より多くのことが言えるためには、\ ``S <: T``\ の導出がどういう形でなければならないかを提示するからです。

練習問題: ★★, optional (sub\_inversion\_Bool)
'''''''''''''''''''''''''''''''''''''''''''''

::

    Lemma sub_inversion_Bool : forall U,
         subtype U ty_Bool ->
           U = ty_Bool.
    Proof with auto.
      intros U Hs.
      remember ty_Bool as V.

練習問題: ★★★, optional (sub\_inversion\_arrow)
'''''''''''''''''''''''''''''''''''''''''''''''

::

    Lemma sub_inversion_arrow : forall U V1 V2,
         subtype U (ty_arrow V1 V2) ->
         exists U1, exists U2,
           U = (ty_arrow U1 U2) /\ (subtype V1 U1) /\ (subtype U2 V2).
    Proof with eauto.
      intros U V1 V2 Hs.
      remember (ty_arrow V1 V2) as V.
      generalize dependent V2. generalize dependent V1.
       Admitted.

☐

正準形(Canonical Forms)
~~~~~~~~~~~~~~~~~~~~~~~

最初に、進行定理の証明はそれほど変わらないことを見ます。1つだけ小さなリファインメントが必要です。問題となる項が関数適用\ ``t1 t2``\ で\ ``t1``\ と\ ``t2``\ が両方とも値の場合を考えるとき、\ ``t1``\ がラムダ抽象の形をしており、そのため\ ``ST_AppAbs``\ 簡約規則が適用できることを確認する必要があります。もともとのSTLCでは、これは明らかです。\ ``t1``\ が関数型\ ``T11->T12``\ を持ち、また、関数型の値を与える規則が1つだけ、つまり規則\ ``T_Abs``\ だけであり、そしてこの規則の結論部の形から、\ ``t1``\ は関数型にならざるを得ない、ということがわかります。

サブタイプを持つSTLCにおいては、この推論はそのままうまく行くわけではありません。その理由は、値が関数型を持つことを示すのに使える規則がもう1つあるからです。包摂規則です。幸い、このことが大きな違いをもたらすことはありません。もし\ ``Gamma |- t1 : T11->T12``\ を示すのに使われた最後の規則が包摂規則だった場合、導出のその前の部分で、同様に\ ``t1``\ が主部(項の部分)である導出があり、帰納法により一番最初には\ ``T_Abs``\ が使われたことが推論できるからです。

推論のこの部分は次の補題にまとめられています。この補題は、関数型の可能な正準形("canonical
forms"、つまり値)を示します。

練習問題: ★★★, optional (canonical\_forms\_of\_arrow\_types)
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''

::

    Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
      has_type Gamma s (ty_arrow T1 T2) ->
      value s ->
      exists x, exists S1, exists s2,
         s = tm_abs x S1 s2.
    Proof with eauto.
       Admitted.

☐

同様に、型\ ``Bool``\ の正準形は定数\ ``true``\ と\ ``false``\ です。

::

    Lemma canonical_forms_of_Bool : forall Gamma s,
      has_type Gamma s ty_Bool ->
      value s ->
      (s = tm_true \/ s = tm_false).
    Proof with eauto.
      intros Gamma s Hty Hv.
      remember ty_Bool as T.
      has_type_cases (induction Hty) Case; try solve by inversion...
      Case "T_Sub".
        subst. apply sub_inversion_Bool in H. subst...
    Qed.

進行
~~~~

進行性の証明は純粋なSTLCとほぼ同様に進みます。ただ何箇所かで正準形補題を使うことを除けば...

「定理」(進行):
任意の項\ ``t``\ と型\ ``T``\ について、もし\ ``empty |- t : T``\ ならば\ ``t``\ は値であるか、ある項\ ``t'``\ について\ ``t ==> t'``\ である。

「証明」:``t``\ と\ ``T``\ が与えられ、\ ``empty |- t : T``\ とする。型付けの導出についての帰納法で進める。

(最後の規則が)\ ``T_Abs``\ 、\ ``T_Unit``\ 、\ ``T_True``\ 、\ ``T_False``\ のいずれかの場合は、自明である。なぜなら、関数抽象、\ ``unit``\ 、\ ``true``\ 、\ ``false``\ は既に値だからである。\ ``T_Var``\ であることはありえない。なぜなら、変数は空コンテキストで型付けできないからである。残るのはより興味深い場合である:

-  型付け導出の最後のステップで規則\ ``T_App``\ が使われた場合、
   項\ ``t1``\ 、\ ``t2``\ と型\ ``T1``\ 、\ ``T2``\ が存在して\ ``t = t1 t2``\ 、\ ``T = T2``\ 、\ ``empty |- t1 : T1 -> T2``\ 、\ ``empty |- t2 : T1``\ となる。さらに帰納法の仮定から、\ ``t1``\ は値であるかステップを進めることができ、\ ``t2``\ も値であるかステップを進めることができる。このとき、3つの場合がある:

   -  ある項\ ``t1'``\ について\ ``t1 ==> t1'``\ とする。このとき\ ``ST_App1``\ より\ ``t1 t2 ==> t1' t2``\ である。
   -  ``t1``\ が値であり、ある項\ ``t2'``\ について\ ``t2 ==> t2'``\ とする。
      このとき規則\ ``ST_App2``\ より\ ``t1 t2 ==> t1 t2'``\ となる。なぜなら\ ``t1``\ が値だからである。

   -  最後に\ ``t1``\ と\ ``t2``\ がどちらも値とする。補題\ ``canonical_forms_for_arrow_types``\ より、\ ``t1``\ はある\ ``x``\ 、\ ``S1``\ 、\ ``s2``\ について\ ``\x:S1.s2``\ という形である。しかしすると\ ``t2``\ が値であることから、\ ``ST_AppAbs``\ より\ ``(\x:S1.s2) t2 ==> [t2/x``\ s2]
      となる。

-  導出の最後のステップで規則\ ``T_If``\ が使われた場合、項\ ``t1``\ 、\ ``t2``\ 、\ ``t3``\ があって\ ``t = if t1 then t2 else t3``\ となり、\ ``empty |- t1 : Bool``\ かつ\ ``empty |- t2 : T``\ かつ\ ``empty |- t3 : T``\ である。さらに、帰納法の仮定より\ ``t1``\ は値であるかステップを進めることができる。

   -  もし\ ``t1``\ が値ならば、ブール値についての正準形補題より\ ``t1 = true``\ または\ ``t1 = false``\ である。どちらの場合でも、規則\ ``ST_IfTrue``\ または\ ``ST_IfFalse``\ を使うことによって\ ``t``\ はステップを進めることができる。
   -  もし\ ``t1``\ がステップを進めることができるならば、
      規則\ ``ST_If``\ より\ ``t``\ もまたステップを進めることができる。

-  導出の最後のステップが規則\ ``T_Sub``\ による場合、型\ ``S``\ があって\ ``S <: T``\ かつ\ ``empty |- t : S``\ となっている。求める結果は型付け導出の帰納法の仮定そのものである。

   Theorem progress : forall t T, has\_type empty t T -> value t /
   exists t', t ==> t'. Proof with eauto. intros t T Ht. remember empty
   as Gamma. revert HeqGamma. has\_type\_cases (induction Ht) Case;
   intros HeqGamma; subst... Case "T\_Var". inversion H. Case "T\_App".
   right. destruct IHHt1; subst... SCase "t1 is a value". destruct
   IHHt2; subst... SSCase "t2 is a value". destruct
   (canonical\_forms\_of\_arrow\_types empty t1 T1 T2) as [x [S1 [t12
   Heqt1]]]... subst. exists (subst t2 x t12)... SSCase "t2 steps".
   destruct H0 as [t2' Hstp]. exists (tm\_app t1 t2')... SCase "t1
   steps". destruct H as [t1' Hstp]. exists (tm\_app t1' t2)... Case
   "T\_If". right. destruct IHHt1. SCase "t1 is a value"... assert (t1 =
   tm\_true / t1 = tm\_false) by (eapply canonical\_forms\_of\_Bool;
   eauto). inversion H0; subst... destruct H. rename x into t1'. eauto.

   Qed.

型付けの反転補題
~~~~~~~~~~~~~~~~

保存定理の証明はサブタイプを追加したことでやはり少し複雑になります。その理由は、上述の「サブタイプの反転補題」と同様に、純粋なSTLCでは「定義から自明」であった(したがって\ ``inversion``\ タクティックからすぐに得られた)のに、サブタイプがあることで本当の証明が必要になった、型付け関係についてのいくつもの事実があるからです。サブタイプがある場合、同じ\ ``has_type``\ の主張を導出するのに複数の方法があるのです。

以下の「反転補題」("inversion
lemma")は、もし、関数抽象の型付け主張\ ``Gamma |- \x:S1.t2 : T``\ の導出があるならば、その導出の中に本体\ ``t2``\ の型を与える部分が含まれている、ということを言うものです。

「補題」:
もし\ ``Gamma |- \x:S1.t2 : T``\ ならば、型\ ``S2``\ が存在して\ ``Gamma, x:S1 |- t2 : S2``\ かつ\ ``S1 -> S2 <: T``\ となる。

(この補題は「\ ``T``\ はそれ自身が関数型である」とは言っていないことに注意します。そうしたいところですが、それは成立しません!)

「証明」:``Gamma``\ 、\ ``x``\ 、\ ``S1``\ 、\ ``t2``\ 、\ ``T``\ を補題の主張に記述された通りとする。\ ``Gamma |- \x:S1.t2 : T``\ の導出についての帰納法で証明する。\ ``T_Var``\ と\ ``T_App``\ の場合はあり得ない。これらは構文的に関数抽象の形の項に型を与えることはできないからである。

-  導出の最後のステップ使われた規則が\ ``T_Abs``\ の場合、型\ ``T12``\ が存在して\ ``T = S1 -> T12``\ かつ\ ``Gamma,x:S1 |- t2 : T12``\ である。\ ``S2``\ として\ ``T12``\ をとると、\ ``S_Refl``\ より\ ``S1 -> T12 <: S1 -> T12``\ となり、求める性質が成立する。
-  導出の最後のステップ使われた規則が\ ``T_Sub``\ の場合、型\ ``S``\ が存在して\ ``S <: T``\ かつ\ ``Gamma |- \x:S1.t2 : S``\ となる。型付け導出の帰納仮定より、型\ ``S2``\ が存在して\ ``S1 -> S2 <: S``\ かつ\ ``Gamma, x:S1 |- t2 : S2``\ である。この\ ``S2``\ を採用すれば、\ ``S1 -> S2 <: T``\ であるから\ ``S_Trans``\ より求める性質が成立する。

   Lemma typing\_inversion\_abs : forall Gamma x S1 t2 T, has\_type
   Gamma (tm\_abs x S1 t2) T -> (exists S2, subtype (ty\_arrow S1 S2) T
   / has\_type (extend Gamma x S1) t2 S2). Proof with eauto. intros
   Gamma x S1 t2 T H. remember (tm\_abs x S1 t2) as t. has\_type\_cases
   (induction H) Case; inversion Heqt; subst; intros; try solve by
   inversion. Case "T\_Abs". exists T12... Case "T\_Sub". destruct
   IHhas\_type as [S2 [Hsub Hty]]... Qed.

同様に...

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
    Qed.

    Lemma typing_inversion_true : forall Gamma T,
      has_type Gamma tm_true T ->
      subtype ty_Bool T.
    Proof with eauto.
      intros Gamma T Htyp. remember tm_true as tu.
      has_type_cases (induction Htyp) Case;
        inversion Heqtu; subst; intros...
    Qed.

    Lemma typing_inversion_false : forall Gamma T,
      has_type Gamma tm_false T ->
      subtype ty_Bool T.
    Proof with eauto.
      intros Gamma T Htyp. remember tm_false as tu.
      has_type_cases (induction Htyp) Case;
        inversion Heqtu; subst; intros...
    Qed.

    Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
      has_type Gamma (tm_if t1 t2 t3) T ->
      has_type Gamma t1 ty_Bool
      /\ has_type Gamma t2 T
      /\ has_type Gamma t3 T.
    Proof with eauto.
      intros Gamma t1 t2 t3 T Hty.
      remember (tm_if t1 t2 t3) as t.
      has_type_cases (induction Hty) Case; intros;
        inversion Heqt; subst; try solve by inversion.
      Case "T_If".
        auto.
      Case "T_Sub".
        destruct (IHHty H0) as [H1 [H2 H3]]...
    Qed.

    Lemma typing_inversion_unit : forall Gamma T,
      has_type Gamma tm_unit T ->
        subtype ty_Unit T.
    Proof with eauto.
      intros Gamma T Htyp. remember tm_unit as tu.
      has_type_cases (induction Htyp) Case;
        inversion Heqtu; subst; intros...
    Qed.

型付けについての反転補題と関数型の間のサブタイプの反転補題は「結合補題」("combination
lemma")としてまとめることができます。この補題は以下で実際に必要になるものを示します。

::

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
~~~~~~~~~~~~~~~~~~

コンテキスト不変性補題は、純粋のSTLCと同じパターンをとります。

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
      | afi_if1 : forall x t1 t2 t3,
          appears_free_in x t1 ->
          appears_free_in x (tm_if t1 t2 t3)
      | afi_if2 : forall x t1 t2 t3,
          appears_free_in x t2 ->
          appears_free_in x (tm_if t1 t2 t3)
      | afi_if3 : forall x t1 t2 t3,
          appears_free_in x t3 ->
          appears_free_in x (tm_if t1 t2 t3)
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
        apply T_Abs... apply IHhas_type. intros x0 Hafi.
        unfold extend. remember (beq_id x x0) as e.
        destruct e...
      Case "T_App".
        apply T_App with T1...
      Case "T_If".
        apply T_If...

    Qed.

    Lemma free_in_context : forall x t T Gamma,
       appears_free_in x t ->
       has_type Gamma t T ->
       exists T', Gamma x = Some T'.
    Proof with eauto.
      intros x t T Gamma Hafi Htyp.
      has_type_cases (induction Htyp) Case;
          subst; inversion Hafi; subst...
      Case "T_Abs".
        destruct (IHHtyp H4) as [T Hctx]. exists T.
        unfold extend in Hctx. apply not_eq_beq_id_false in H2.
        rewrite H2 in Hctx...  Qed.

置換
~~~~

置換補題(*substitution
lemma*)は純粋なSTLCと同じ流れで証明されます。唯一の大きな変更点は、いくつかの場所で、部分項が型を持つことについての仮定から構造的情報を抽出するために、Coqの\ ``inversion``\ タクティックを使う代わりに上で証明した反転補題を使うことです。

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
         has_type (extend Gamma x U) t S  ->
         has_type empty v U   ->
         has_type Gamma (subst v x t) S.
    Proof with eauto.
      intros Gamma x U v t S Htypt Htypv.
      generalize dependent S. generalize dependent Gamma.
      tm_cases (induction t) Case; intros; simpl.
      Case "tm_var".
        rename i into y.
        destruct (typing_inversion_var _ _ _ Htypt)
            as [T [Hctx Hsub]].
        unfold extend in Hctx.
        remember (beq_id x y) as e. destruct e...
        SCase "x=y".
          apply beq_id_eq in Heqe. subst.
          inversion Hctx; subst. clear Hctx.
          apply context_invariance with empty...
          intros x Hcontra.
          destruct (free_in_context _ _ S empty Hcontra)
              as [T' HT']...
          inversion HT'.
      Case "tm_app".
        destruct (typing_inversion_app _ _ _ _ Htypt)
            as [T1 [Htypt1 Htypt2]].
        eapply T_App...
      Case "tm_abs".
        rename i into y. rename t into T1.
        destruct (typing_inversion_abs _ _ _ _ _ Htypt)
          as [T2 [Hsub Htypt2]].
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
      Case "tm_true".
          assert (subtype ty_Bool S)
            by apply (typing_inversion_true _ _  Htypt)...
      Case "tm_false".
          assert (subtype ty_Bool S)
            by apply (typing_inversion_false _ _  Htypt)...
      Case "tm_if".
        assert (has_type (extend Gamma x U) t1 ty_Bool
                /\ has_type (extend Gamma x U) t2 S
                /\ has_type (extend Gamma x U) t3 S)
          by apply (typing_inversion_if _ _ _ _ _ Htypt).
        destruct H as [H1 [H2 H3]].
        apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
        auto.
      Case "tm_unit".
        assert (subtype ty_Unit S)
          by apply (typing_inversion_unit _ _  Htypt)...
    Qed.

保存
~~~~

(型の)保存の証明は以前の章とほとんど同じです。適切な場所で置換補題を使い、型付け仮定から構造的情報を抽出するために上述の反転補題をまた使います。

「定理」(保存)：\ ``t``\ 、\ ``t'``\ が項で\ ``T``\ が型であり、\ ``empty |- t : T``\ かつ\ ``t ==> t'``\ ならば、\ ``empty |- t' : T``\ である。

「証明」:``t``\ と\ ``T``\ が\ ``empty |- t : T``\ であるとする。証明は、\ ``t'``\ を特化しないまま型付け導出の構造に関する帰納法で進める。(最後の規則が)\ ``T_Abs``\ 、\ ``T_Unit``\ 、\ ``T_True``\ 、\ ``T_False``\ の場合は考えなくて良い。なぜなら関数抽象と定数はステップを進めないからである。\ ``T_Var``\ も考えなくて良い。なぜならコンテキストが空だからである。

-  もし導出の最後のステップの規則が\ ``T_App``\ ならば、
   項\ ``t1``t2``\ と型\ ``T1``T2``\ が存在して、\ ``t = t1 t2``\ 、\ ``T = T2``\ 、\ ``empty |- t1 : T1 -> T2``\ 、\ ``empty |- t2 : T1``\ である。
   ステップ関係の定義から、\ ``t1 t2``\ がステップする方法は3通りである。\ ``ST_App1``\ と\ ``ST_App2``\ の場合、型付け導出の帰納仮定と\ ``T_App``\ より求める結果がすぐに得られる。
   ``t1 t2``\ のステップが\ ``ST_AppAbs``\ によるとする。するとある型\ ``S``\ と項\ ``t12``\ について\ ``t1 = \x:S.t12``\ であり、かつ\ ``t' = [t2/x``\ t12]
   である。
   補題\ ``abs_arrow``\ より、\ ``T1 <: S``\ かつ\ ``x:S1 |- s2 : T2``\ となる。すると置換補題(``substitution_preserves_typing``)より、\ ``empty |- [t2/x``\ t12
   : T2] となるがこれが求める結果である。

   -  もし導出の最後のステップで使う規則が\ ``T_If``\ ならば、
      項\ ``t1``\ 、\ ``t2``\ 、\ ``t3``\ が存在して\ ``t = if t1 then t2 else t3``\ かつ\ ``empty |- t1 : Bool``\ かつ\ ``empty |- t2 : T``\ かつ\ ``empty |- t3 : T``\ となる。さらに帰納法の仮定より、もし\ ``t1``\ がステップして\ ``t1'``\ に進むならば\ ``empty |- t1' : Bool``\ である。\ ``t ==> t'``\ を示すために使われた規則によって、3つの場合がある。

   -  ``t ==> t'``\ が規則\ ``ST_If``\ による場合、\ ``t' = if t1' then t2 else t3``\ かつ\ ``t1 ==> t1'``\ となる。帰納法の仮定より\ ``empty |- t1' : Bool``\ となり、これから\ ``T_If``\ より\ ``empty |- t' : T``\ となる。
   -  ``t ==> t'``\ が規則\ ``ST_IfTrue``\ または\ ``ST_IfFalse``\ による場合、\ ``t' = t2``\ または\ ``t' = t3``\ であり、仮定から\ ``empty |- t' : T``\ となる。

-  もし導出の最後のステップで使う規則が\ ``T_Sub``\ ならば、
   型\ ``S``\ が存在して\ ``S <: T``\ かつ\ ``empty |- t : S``\ となる。型付け導出についての帰納法の仮定と\ ``T_Sub``\ の適用から結果がすぐに得られる。☐

   Theorem preservation : forall t t' T, has\_type empty t T -> t ==> t'
   -> has\_type empty t' T. Proof with eauto. intros t t' T HT. remember
   empty as Gamma. generalize dependent HeqGamma. generalize dependent
   t'. has\_type\_cases (induction HT) Case; intros t' HeqGamma HE;
   subst; inversion HE; subst... Case "T\_App". inversion HE; subst...
   SCase "ST\_AppAbs". destruct (abs\_arrow \_ \_ \_ \_ \_ HT1) as [HA1
   HA2]. apply substitution\_preserves\_typing with T... Qed.

型付けの練習問題
~~~~~~~~~~~~~~~~

練習問題: ★★ (variations)
'''''''''''''''''''''''''

この問題の各部分は、Unitとサブタイプを持つSTLCの定義を変更する別々の方法を導きます。(これらの変更は累積的ではありません。各部分はいずれも元々の言語から始まります。)各部分について、(進行、保存の)性質のうち偽になるものをリストアップしなさい。偽になる性質について、反例を示しなさい。

-  次の型付け規則を追加する:

   ::

                               Gamma |- t : S1->S2
                       S1 <: T1      T1 <: S1     S2 <: T2
                       -----------------------------------              (T_Funny1)
                               Gamma |- t : T1->T2

-  次の簡約規則を追加する:

   ::

                                ------------------                     (ST_Funny21)
                                unit ==> (\x:Top. x)

-  次のサブタイプ規則を追加する:

   ::

                                  --------------                        (S_Funny3)
                                  Unit <: Top->Top

-  次のサブタイプ規則を追加する:

   ::

                                  --------------                        (S_Funny4)
                                  Top->Top <: Unit

-  次の評価規則を追加する:

   ::

                                -----------------                      (ST_Funny5)
                                (unit t) ==> (t unit)

-  上と同じ評価規則と新たな型付け規則を追加する:

   ::

                                -----------------                      (ST_Funny5)
                                (unit t) ==> (t unit)

                              ----------------------                    (T_Funny6)
                              empty |- Unit : Top->Top

-  関数型のサブタイプ規則を次のものに変更する:

   ::

                             S1 <: T1       S2 <: T2
                             -----------------------                    (S_Arrow')
                                  S1->S2 <: T1->T2

☐

練習問題: 直積の追加
--------------------

練習問題: ★★★★, optional (products)
'''''''''''''''''''''''''''''''''''

定義したシステムに対、射影、直積型を追加することは比較的簡単な問題です。次の拡張を行いなさい:

-  ``ty``\ と\ ``tm``\ の定義に、対のコンストラクタ、第1射影、第2射影、直積型を追加しなさい。
   (``ty_cases``\ と\ ``tm_cases``\ に対応する場合を追加することを忘れないこと。)
-  自明な方法で、well-formedness 関係を拡張しなさい。
-  操作的意味に前の章と同様の簡約規則を拡張しなさい。
-  サブタイプ関係に次の規則を拡張しなさい:

   ::

                           S1 <: T1     S2 <: T2
                           ---------------------                     (Sub_Prod)
                             S1 * S2 <: T1 * T2

-  型付け関係に、前の章と同様の、対と射影の規則を拡張しなさい。
-  進行および保存の証明、およびそのための補題を、
   新しい構成要素を扱うように拡張しなさい。(完全に新しいある補題を追加する必要もあるでしょう。)☐


