# OPERATORS

操作符一组一起执行一个任务的语句，程序员可能会把它称为函数，你使用一个 `==`来定义它们。

```c++
Five == 5
Five + 5 \* 10
```

你也可以给它们参数

```c++
IsFive(x) == x = 5
```

或者多个参数

```c++
SumWithFive(a, b) == a + b + 5
```

你可以在任何使用其他表达式的地方使用操作符。

> Tip



## 高阶运算符

你可以使用特殊的语法编写高阶运算符调用其他的运算符：

```
Sum(a, b) == a + b
Do(op(_,_), a, b) == op(a, b)

Do(Sum, 1, 2) = 3
```

如果在调用之前使用`RECURSIVE`指定操作符，也可以进行操作符递归:

```
RECURSIVE SetReduce(_, _, _)

SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == CHOOSE s \in S: TRUE
                                   IN SetReduce(Op, S \ {s}, Op(s, value)) 

CandlesOnChannukah == SetReduce(Sum, 2..9, 0) \* 44
```



## 结合PlusCal

如果你的操作符不引用任何PlusCal变量(如`IsEmpty(S) == S = {}`)，那么您可以将其置于PlusCal算法的开始之上，它将像其他表达式一样可用。

如果你的操作符确实引用任何PlusCal变量(比如`HasMoneyLeft == money > 0`，那么它必须出现在算法中或之后。第一个方法是把它放在TLA+翻译之后。这很简单，但也意味着PlusCal不能调用这个操作符。这对不变量很好，对条件不太好。要将运算符直接放在代码中，可以使用`define`定义代码块:

```
define
  Foo(bar) == baz
  \* ...
end define
```