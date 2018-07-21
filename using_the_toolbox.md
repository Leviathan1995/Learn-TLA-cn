# 使用ToolBox

我们编写specifications的目的是为了发现隐藏在specifications中的错误。为此，我们首先需要将我们的PlusCal代码转换为TLA+，然后告诉模型检查器要查找什么。这两个都有点棘手。幸运的是，我们有一个可用的IDE，叫做[TLA+ Toolbox](https://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html)。我们将使用以下示例作为介绍：

```sql
---- MODULE example ----
EXTENDS Integers

(* --algorithm example
variables x = 5
begin
 Add:
  x := x + 1;
end algorithm; *)
====
```

创建一个新的spec（记住名字必须匹配）并将其复制进去。运行转换器，首先你会看到你的文件被这样更新了：

```sql
\* BEGIN TRANSLATION

A WHOLE LOTTA STUFF

\* END TRANSLATION
```

这是生成的TLA +。关于为什么我们要从PlusCal开始，可能现在说得通了。不过别担心，我们将在下一章深入介绍TLA+，因此目前你不需要完全理解整个翻译。但这就是我们要进行模型检查的实际代码：

下一步，我们新建一个model，告诉TLC需要检查什么。我们感兴趣的部分是overview，应该是这样的:

![model_overview](/assets/model_overview.png)

Terms:

* **Model Description：**没有什么意义，只是文档。
* **What is the behavior spec?**：暂时把它放在“时间公式”上。
* **What is the model?:** 我们将在“Models”一章中讨论这个问题。
* **What to check?:**这就是我们所关心的，
  * *Deadlock*检查程序本身不能捕获22。
  * *Invariants*检查某个方程，例如`x = TRUE`，对于TLC可以达到的所有可能状态都是正确的。
  * *Temporal*属性检查所有可能的行为是否为真，即“生存期”。例如，“x从TRUE切换到FALSE并返回”。
* **How to run?:** 运行时优化。这是超出范围的。

我们可以通过单击左上方的绿色箭头来运行模型。TLC将搜索整个状态空间，在我们的不变量中寻找可能的错误。由于我们实际上还没有设置任何不变量，它不会发现任何失败，所以这将是成功的。注意，它列出了直径为2，不同状态数为2。前者意味着最长的状态空间的步数有两步:  初始状态`x = 5`和`Add`之后`x = 6`。因为只有一个可能的起始状态，所以总共有两个不同的状态：

![model_run](/assets/model_run.png)

如果我们把`x = 5`换成`x \in 1..5`会发生什么？重新转换算法并重新运行模型。你会看到，虽然最长的状态空间的步数仍然是2，但现在有10个不同的状态。由于有5个潜在的初始值，TLC将运行带有所有这些值的模型，以防其中一个值违反不变量(虽然还是没有设置)。

那么，让我们添加一个会失败的不变量吧。回到模型概述，并将`x /= 6`添加到“不变量”部分，这个不变量意味着我们的程序的x的值不会是6。很明显，当x = 5时它就失效了，这是可能的初始状态之一。当我们重新运行模型时，我们会得到这样的结果：

![model_run](/assets/invariant.png)

![model_run](/assets/error_trace.png)

这不仅向我们展示了什么是失败的，也向我们展示了它是如何失败的。在这种情况下，“初始状态谓词”告诉我们起始状态：x是5。下面的“动作”行显示“添加”步骤已经完成，x变为6，这将使我们的不变量无效。

### 计算表达式

我们切换回Model的overview部分。将行为规范更改为“no behavior spec”。这告诉TLC，你正在建模的系统是不存在的，你只是在尝试TLA+语法。我们不能在这里运行任何东西。但是我们可以做的是到“模型检查结果”选项中，把TLA放到“evaluate constant expression”中。试着输入`CHOOSE y \in {1, 2, 3} : y*y = 4`在这个选项中，然后重新运行模型。您应该会在”Value”框中看到`2`。

我们不会使用“no behavior spec”模式来测试实际系统，但它是一个很好的工具，可以测试您理解一些TLA+表达式是如何工作的。别担心，当我们深入到TLA+时，我们会重新介绍这一点。