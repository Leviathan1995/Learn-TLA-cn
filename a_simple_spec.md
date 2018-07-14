# A SIMPLE SPEC

TLA+最初是一种表示法，模型检查器TLC在5年后才问世。由于TLA+并未打算运行，所以有人认为它只是一个可读的文档，而不是可运行的代码。这意味着我们需要先完成一些模板。

为了让TLC分析specifying，它必须具有以下格式:

```
---- MODULE module_name ----
\* TLA+ code

(* --algorithm algorithm_name
begin
\* PlusCal code
end algorithm; *)
====
```

TLC只分析`----`开始和`====`结束之间的代码。任何超出这些界限的东西都会被忽略。`module_name`必须与文件名相同，而`algorithm_name`可以是任何您想要的内容。`\*`是行注释，`(*`是块注释。注意，我们把算法放到注释中。如果不把它放到注释中，就会出现语法错误，因为PlusCal不是TLA+。

每个文件只能有一个PlusCal算法。

对于PlusCal本身，这是一个基本单线程的算法的布局：

```sql
variables x = 1, y \in {3, 4}, z = {3, 4};
begin
  \* your code here
end algorithm;
```

在`variables`块中`=`是赋值。在其他地方，`=`是等式检查，而`:=`是赋值。

你可能已经注意到`y \in {3, 4}`。这是集合的定义，这意味着对于这个算法，y可以是3或4。当你检查模型时，TLC会确保它适用于y的**所有**可能值，它首先会测试`y = 3`时没有任何失败，然后测试`y = 4`时没有任何失败。

将`y \in{3,4`}与`z ={3,4}`进行比较的话，z是集合`{3,4}`。任何类型的数据结构都可以在TLA+中分配给一个变量。



让我们从Hello World开始

```sql
EXTENDS TLC

(* --algorithm hello_world
variable s \in {"Hello", "World!"};
begin
  A:
    print s;
end algorithm; *)
```

`EXTENDS`是TLA+的`#include`模拟。`TLC`是一个包括了`print`和`assert`的模块。顺便说一下，`print`是唯一可以使用TLA+的IO，它是为调试目的而提供的。

这里唯一不同的是`A:`，这是标签。TLC将标签视为规范中的“步骤”；标签里的一切都同时发生。只有在标签之间，模型才能检查不变量和切换进程。同样，您不能在同一个标签中两次分配同一个变量。在大多数情况下，它在这里并不是很有用，但以后会非常重要。

我想你对其他编程语言很熟悉。为了使建模更熟悉，PlusCal有类似的结构。语义非常明显，下面是它们的样子。假设所有变量都已经初始化，并且我们处于一个`begin`块中。

### 逻辑运算符

| logic     | operator | `TRUE`          | `FALSE`          |
| --------- | -------- | --------------- | ---------------- |
| equal     | `=`      | `1 = 1`         | `1 = 2`          |
| not equal | `/=`     | `1 /= 2`        | `1 /= 1`         |
| and       | `/\`     | `TRUE /\ TRUE`  | `TRUE /\ FALSE`  |
| or        | `\/`     | `FALSE \/ TRUE` | `FALSE \/ FALSE` |
| not       | `~`      | `~FALSE`        | `~TRUE`          |

### If

```c++
if x = 5 then
  skip;
elsif x = 6 then
  skip;
else
  skip;
end if;
```

### While

```c++
x := 5;
while x > 0 do
  x := x - 1;
end while;
```

这是唯一的循环形式。

### Goto

```c++
A:
  if TRUE then goto B else goto C endif;
B:
  skip;
C:
  skip;
```

Goto在PlusCal中是非常有用的。