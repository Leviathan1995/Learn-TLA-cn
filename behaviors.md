# 行为

到目前为止，我们已经了解了PlusCal的基本知识以及如何运行模型。我们还看到，如果我们的起始变量被指定为一个集合，它将扩展TLC可以搜索的状态空间。这需要我们编写有用的specifications。最后一步是添加不同的行为：允许系统在给定的步骤中做不同的事情。在单一的进程PlusCal算法中，有两种简单的方式来引入并发性：`with`语句和`either`语句。

## Either

`either`看起来都很像一个基本的if语句。其语法如下：

```sql
either
  skip;
or
  skip;
or
  skip;
end either;
```

需要注意的是TLC将运行每个分支。当它遇到任意一个时，它创建一个单独的行为并为每个行为执行一个不同的分支。例如：

```sql
variables x = 3, i = 2;
begin
while i > 0 do
  either 
    x := x + 2;
  or 
    x := x * 2;
  end either;
  i := i - 1;
end while
```

内循环将发生两次。每次模型可以添加两个或两个x，这意味着有四个可能的最终结果:

![model_run](/assets/behaviors_result.png)



## With

`with`的作用的是一样的，除了为每个可能的分支创建一个新的行为之外，它还为集合中的每个元素创建一个行为。在下面的情况下，我们有三个可能的行为:

```
with a \in {1, 2, 3} do
  x := x + a
end with;
```

这将为集合中的每个元素创建一个单独的时间线。

![model_run](/assets/with_result.png)



## 例子

描述一个系统，该系统有三个标志，打开和关闭，还有一个更改标志的状态。

现在我们在实际操作上有一些限制，但是我们已经可以开始构建简单的模式了。这里有一种写法：

```sql
---- MODULE flags ----
EXTENDS TLC, Integers
(* --algorithm flags
variables f1 \in BOOLEAN, f2 \in BOOLEAN, f3 \in BOOLEAN
begin
  while TRUE do
    with f \in {1, 2, 3} do
      if f = 1 then
        either
          f1 := TRUE;
        or
          f1 := FALSE;
        end either;
      elsif f = 2 then
        either
          f2 := TRUE;
        or
          f2 := FALSE;
        end either;
      else
        either
          f3 := TRUE;
        or
          f3 := FALSE;
        end either;
      end if;
    end with;
  end while;
end algorithm; *)

====
```

这并不是最理想的写法，但我想在这里同时展示`with`和`either`。你可以用这两种方法。`BOOLEAN`是一个TLA+内建，它等于集合`{TRUE, FALSE}`。如你所见，每一步都选择一个标志，并将其设置为true或false。如果觉得麻烦，我们可以这样写:

```sql
---- MODULE flags ----
EXTENDS TLC, Integers
(* --algorithm flags
variables flags \in [1..3 -> BOOLEAN], next = TRUE;
begin
  while next do
    with f \in DOMAIN flags, n \in BOOLEAN do
      flags[f] := ~flags[f];
      next := n;
    end with;
  end while;
end algorithm; *)

====
```

The `flags \in [1..3 -> BOOLEAN]` 叫做一个[函数式集合](functions.md)，后面的内容会涉及。