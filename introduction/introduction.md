# 介绍

#### 什么是TLA+?

TLA+是一个形式化描述语言\(_formal specification language\)，_它是一种用来程序化的验证系统或算法的设计不存在严重bug的工具，某种意义上来说等价于软件的蓝图。

### 为什么我们需要使用它?

这里有一个描述用户交易一个唯一的物品的TLA+例子:

```
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

既然我们要检查一件物品的拥有者是交易后的那个人，我们就应该对诈骗保持安全的警惕，对吧? 但是当我们对模型进行检查的时候，我们发现这个这个设计是错误的: Alice不能交易一个物品给他自己。

并且在检查运行完成之前，

But if we run the model checker, we find that’s not true: Alice could trade an item to

_herself_

and, before that process finishes running, resolve a parallel trade giving that same item to Bob. Then the first trade resolves and Alice gets the item back. Our algorithm fails for race conditions, and we know this because TLA+ explored every possible state and timeline.

