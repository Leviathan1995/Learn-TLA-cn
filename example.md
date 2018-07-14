# 例子

一般来说，模型检查在理论上似乎很有吸引力，但人们常常怀疑它是否能在实践中使用。因此，这里有一个指导示例，说明如何实现一个简单的例子并查找错误。**这个例子不需要理解教程的其他部分**。这里的所有内容将在接下来的章节中更详细地介绍。不过，提前获得一些实践经验还是值得的。

## 问题

你要为银行写一个软件，目前有Alice和Bob两个客户，他们俩每个人都有固定数目的钱在他们的账户，Alice希望转一些钱给Bob，假如只专注于他们的这两个账户，该如何实现这个模型呢?

### 第一步

```PlusCal
---- MODULE transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money = 5;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;

end algorithm *)
====
```

在我们开始研究它之前，我们先来分解一下当前的语法。由于TLA+是一种规范的描述语言，它对程序的结构施加了一定的限制。

* 如果文件名是"transfer", specification的第一行必须是`---- MODULE transfer ----`，而且必须在两边保留至少四个破折号，并且在最后一行必须有至少四个等号，在此之外的所有代码都会被忽略。
* `EXTENDS` 等同于其他语言`import` 语句。
* `\*`代表注释，`(* *)`代表注释块。需要注意的是：整个算法都写在注释块里。是故意这样做的，因为PlusCal描述的算法不是语法有效的TLA+，所以我们不能在TLA文件中运行它。因此，将它们放在注释中，然后让PlusCal翻译器翻译整个算法。
* 注意，在声明变量时我们使用`=`，而在算法实现中我们使用`:=`。变量定义之外的`=`是比较运算符，不等号是`/=`。例如: `1 + 2 = 3;2 + 3 /= 4`。
* `A:`、` B:`是标签\(label\)。它们定义了算法的步骤，理解标签如何工作对于编写更复杂的算法至关重要，因为它们定义了并发性可能严重出错的地方。我们稍后会更深入地研究它们。

那么我们该如何运行呢？呃，目前还不能。首先，它不是真正的代码，我们必须先把它转译出来。而且，我们也不直接“运行”它。相反，我们需要设计模型来测试它。让我们现在就开始吧。

### TLA+ Toolbox {#tla-toolbox}

TLA+ Toolbox 是一个TLA+的IDE，无论你的偏好是什么，使用IDE都是一个非常正确的选择。

![img1](/assets/import.png)

让我们来打开IDE，添加第一个项目，关于specification有两部分：Modules和Models。Modules包括我们的代码，Models测试它们。我们首先新建一个新的specification，然后将它转换为TLA+ \(Mac上直接使用`⌘T`\)

![img2](/assets/import1.png)

转换之后你将看到一堆代码出现，这就是我们的PlusCal算法的TLA+翻译，也就是模型检查器实际检查的东西。说到这里，我们也来创建一个模型:

![img3](/assets/import2.png)

这个模型目前是空的，即使没有任何的配置，我们也可以在下一节直接使用它。

### 断言和集合{#assertions-and-sets}

Alice的账户会成为负值吗？虽然我们的specification现在允许这样，但是却不是我们想要的。我们可以在交易完成之后加一个基本的断言检查，TLA+的断言和其他语言的断言类似。但是在TLA+中，它通常用来调试，在这个例子中，TLA+拥有更强大的工具来检查合同和财产的正确性。

这里就是我们加了断言的代码:

```sql
---- MODULE transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money = 5;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;
C: assert alice_account >= 0;
end algorithm *)
=====
```

如果我们运行整个模型，会发现它是可以通过的。

至少，它适用于我们尝试的那个数字。 这并不意味着它适用于所有情况。 在测试时，通常很难选择恰当的测试用例来表示你想要查找的错误。 这是因为大多数语言都可以轻松测试特定的状态，但不能测试大量的状态。 但是在TLA+中，可以测试范围很广：

```sql
---- MODULE transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;
C: assert alice_account >= 0;
end algorithm *)
=====
```

这里我们只做了一个变动：将`money = 5`修改为`money \in 1..20`，这个变动将算法里面的`money`的数值变化改为可以从1到20，所以检查模型时就有20种可能的状态: `(10, 10, 1), (10, 10, 2), ...`。TLA+将尝试所有的二十种可能性，并查看它们是否触发断言。这里我们还可以继续扩展：`alice_account \in {5, 10}`，这时候就有40种可能的状态了。

（`{}`是集合。`a..b`是语法糖，代表"a和b之间所有整数的集合"，所以`1..3` = `{1,2,3}`）

现在当我们运行模型检查时，我们会发现得到了一个错误：

![img4](/assets/model_assert_fail.png)

我们可以通过将整个检查包在一个`If`代码块中来解决这个问题：

```
---- MODULE transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
    B: bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;
end algorithm *)
=====
```

现在可以正常运行了。

这更接近于测试所有可能的情况，但仍然没有测试所有可能的情况。如果`money`是`4997`，算法会出错吗？ 如果我们真的想测试所有可能的情况，我们可以将`money \in 1..20`替换为`money \in Nat`，其中Nat是自然数字的集合。 这在TLA+是完全有效的。 不幸的是，它也是模型检查器无法处理的东西。 TLC只能检查TLA +的子集，而无限集不是其中的一部分。



### TLA+和常量

你能汇一笔负数的钱吗？ 我们可以在算法的开头添加一个断言：`assert money > 0`。 不过，这一次，我们将介绍一种新方法，为下一节做准备：

```sql
---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
    B: bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;

end algorithm *)

\* BEGIN TRANSLATION
\* Removed for clarity...
\* END TRANSLATION

MoneyNotNegative == money >= 0

====
```

这里有一个多出来的部分，需要注意的是： 首先，这不是PlusCal算法的一部分。 这是我们放在文件底部的纯TLA +，以便能够引用转换后的TLA+。 只要在`END TRANSLATION`标记之后，TLA+就可以引用你的PlusCal所能提供的任何东西。 其次，它没有改变任何东西。 相反，它是系统的属性。 如果`money`是负数，`MoneyNotNegative`是`false`，否则就是`true`。

这与断言有什么不同？ 断言检查在一个地方。 我们可以将`MoneyNotNegative`指定为系统的常量，在所有可能的系统状态中都必须为`true`。 它成为模型的一部分，然后它将在从Alice的账户中提取资金之前进行检查，即存款和提款等操作。如果我们设置`money = 1`，当我们添加`money := money - 2`这一步时，`MoneyNotNegative`在任何一个状态下都会被捕获。



### 再进一步：检查原子性

到目前为止，我们还没有做过任何与众不同的事情。 到目前为止，通过单元测试，我们所做的一切都可以在真实系统中轻松覆盖。 但我想表明我们已经可以使用我们学到的东西来找到更复杂的错误。 Alice想给Bob1000美元。 如果我们运气不好，它可能会像这样：

* 系统检查Alice拥有足够的money
* 从Alice的账户减去$1000
* Eve用棒球棒猛击服务器
* Bob并没有收到这笔钱
* $1000完全从整个系统中消失了
* 证券交易委员会以欺诈为由将你的银行关闭。

我们已经有了完整的工具链来检查这个问题了。首先，我们需要弄清楚如果表示被我们可以通过要求系统中的总资金总是相同的来实现这一点:

```sql
---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20,
          account_total = alice_account + bob_account;

begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
    B: bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;

end algorithm *)

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

====
```

然后，我们在模型中声明这个要被检查的常量:

![img5](/assets/model_moneyinvariant1.png)

![img6](/assets/model_moneyinvariant2.png)

当我们运行的时候，TLC发现了一个反例：在步骤a和步骤B之间，常量不成立。

![img7](/assets/model_moneyinvariant_fail.png)

我们怎么解决这个问题?它取决于我们关心的抽象级别。如果您正在设计一个数据库，那么您需要指定保持系统一致性所需的确切步骤。但是，在我们的级别上，我们可能可以访问数据库事务，并可以“抽象出”原子性检查。我们的方法是将A和B合并为一个“事务”步骤。这告诉TLA+这两种操作同时发生，并且系统永远不会通过无效的状态。

```sql
---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20,
          account_total = alice_account + bob_account;

begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
       bob_account := bob_account + money; \* Both now part of A
end if;
C: assert alice_account >= 0;

end algorithm *)

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

====
```



### 多进程算法

作为示例的最后一部分，让我们讨论并发性。现在我们的体系似乎足够稳定，两党之间的一场交易。但是，如果人们可以进行多次转账，会发生什么呢?每个帐户都使用相同的帐户状态，但彼此独立操作。我们能测试那个系统的行为吗?

PlusCal支持多处理算法。过程可以是完全不同的算法同时发生，也可以是相同的算法并行发生(或者两者都发生)。后者是我们想要说明的。

```sql
---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10,
          account_total = alice_account + bob_account;

process Transfer \in 1..2
  variable money \in 1..20;
begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
       bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;
end process

end algorithm *)

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

====
```

账户是全局变量，而货币是过程的局部变量。这意味着有400个可能的初始状态，因为第一个转移可以是1美元，第二个是7美元。然而，实际上有2400种可能的行为!这是因为TLC可以选择运行进程的顺序，以及如何插入它们。

然而，钱不再是负数了，因为现在有两种货币的价值。如果您将其添加到模型中，请确保取消检查以避免错误并重新运行。您应该得到以下错误:

![img8](/assets/multiprocess_fail.png)

当我们检查Alice是否有足够的钱时和我们实际转账时之间是有差距的。对于一个过程来说，这不是问题，但是对于两个过程来说，这意味着她的账户可以变成负数。TLC足够好，可以提供复制错误所需的初始状态和步骤。

此示例仅涵盖工具的一小部分;我们甚至还没有接触到时间属性、活跃度或设置操作。不过，希望这已经向您表明，即使是对TLA+的粗略了解也足以发现有趣的问题。