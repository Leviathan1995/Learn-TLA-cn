## 什么是TLA+？

TLA+是一种形式化描述语言。它是一种以程序化的方式验证设计的系统或算法是否存在严重的Bug。它是相当于蓝图的软件。

## 为什么要用它？

这是一个简单的TLA+例子，描述了人们交易一个唯一的物品的场景。你能找到其中的bug吗？

```python
People == {"alice", "bob"}
Items == {"ore", "sheep", "brick"}
(* --algorithm trade
variable owner_of \in [Items -> People]

process giveitem \in 1..3 \* up to three possible trades made
variables item \in Items, 
          owner = owner_of[item], 
          to \in People,
          origin_of_trade \in People
begin Give:
    if origin_of_trade = owner then 
        owner_of[item] := to;
    end if;
end process;
end algorithm; *)
```

我们需要检查项目的所有者是否是交易它的人，这样我们保证交易的安全性，对吧？但是如果我们运行模型检查器，我们发现这里是存在问题的：**Alice可以将物品交易给自己**，并且我们的算法在竞态条件(race condition)下也会产生问题。为什么我们知道能知道这一点，因为TLA +会发现所有可能的状态和时间线。

这里有几种不同的方法来解决这个问题。但我们的解决方案是否适用于多余两个人的交易？在TLA+中，检查这一点很简单，只需要修改为`People == {“alice”，“bob”，“eve”}`。如果我们可以一次交易多个项目，它会起作用吗？ `variable items \in SUBSET Items`。如果有多只绵羊，矿石和砖块呢？`amount_owned = [People \X Items -> 0..5]`。算法可能处于的所有状态，都会被TLA+检查到。

##  这是一个初学者友好的指南吗？

你好！本指南以简单实用的方式介绍了TLA +的基础知识。如果您想从头开始，您需要了解我们在[这里](about-this-guide.md)介绍的内容。如果你想先直接深入进来，可以先尝试这个[新的例子](example.md)？

无论哪种方式，欢迎来到TLA+！
