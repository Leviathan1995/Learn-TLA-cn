# 例子

一般来说，模型检查在理论上似乎很有吸引力，但人们常常怀疑它是否能在实践中使用。因此，这是一个指导示例，说明如何实现一个简单的描述并查找错误。这个例子对于理解本指南的其余部分是没有必要的。这里的所有内容将在接下来的章节中更详细地介绍。不过，获得一些实践经验还是值得的。

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
* `\*`代表注释，\`\`代表注释块。需要注意的是：整个算法都写在注释块里。这是故意的，因为PlusCal描述的算法不是语法有效的TLA+，所以我们不能在TLA文件中运行它。因此，将它们放在注释中，然后让PlusCal翻译器翻译整个算法。
* 注意，在声明变量时我们使用`=`，而在算法实现中我们使用`:=`。变量定义之外的`=`是比较运算符，不等号是`/=`。例如: `1 + 2 = 3;2 + 3 /= 4`。
* A: B:是标签\(label\)。它们定义了算法的步骤，理解标签如何工作对于编写更复杂的算法至关重要，因为它们定义了并发性可能严重出错的地方。我们稍后会更深入地研究它们。

那么我们该如何运行呢？嗯,我们不能。首先，它不是真正的代码，我们必须先把它转译出来。而且，我们也不直接“运行”它。相反，我们需要设计模型来测试它。让我们现在就开始吧。

### TLA+ Toolbox {#tla-toolbox}

TLA+ Toolbox 是一个TLA+的IDE，无论你的偏好如何，使用IDE都是一个非常正确的选择。![](/assets/import.png)

让我们来打开IDE，添加第一个项目，关于specification有两部分: modules和models。modules包括我们的代码，models测试它们。我们首先新建一个新的specification，然后将它转换为TLA+ \(Mac上直接使用`⌘T`\)

![](/assets/import1.png)

转换之后你将看到一堆代码出现，这就是我们的PlusCal算法的TLA+翻译，也就是模型检查器实际检查的东西。说到这里，我们也来创建一个模型:[          
](https://learntla.com/introduction/example/img/translated.png)![](/assets/import2.png)这个模型目前是空的，即使没有任何的配置，我们也可以在下一节直接使用它。

### Assertions and Sets {#assertions-and-sets}

Alice的账户将会成为负值

