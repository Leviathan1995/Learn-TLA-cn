# ABOUT THIS GUIDE

这本教程重点介绍尽可能快地启动和运行所需的最低要求，以及一些改进模型的中间技术。这种方法将忽略或略过绝大多数TLA +，以便使这个小块更容易学习。这并不意味着其他部分无聊，困难或无用。离得很远。但它们超出了本指南的范围。

假设你有以下背景：

* **你是一位经验丰富的程序员**。这本教程不是教授如何去编程，并且TLA+也不是一个用户友好的工具。
* **你熟悉测试**。如果您之前没有使用过单元测试，那么这比学习它更有用。
* **你知道一些数学**。 TLA+大量借鉴数学结构和语法。如果你听说过de Morgan定律，知道什么是集合，并且能够理解什么`(P => Q) => (~Q => ~P)`是什么意思。否则，虽然你仍然可以学习TLA+，但可能不太直观。

**你需要下载[TLA+ Toolbox](https://github.com/tlaplus/tlaplus/releases/latest)**, 并且确保你还能获取以下资源:

* [PlusCal手册](https://research.microsoft.com/en-us/um/people/lamport/tla/pluscal.html)：PlusCal是TLA+的算法接口。我们将在本指南中介绍它的所有内容，但是有一个完整的语法参考是很好的。
* [TLA + Cheat Sheet](http://lamport.azurewebsites.net/tla/summary-standalone.pdf)：这里包括本教程范围之外的语法。
* [Specifying Systems](https://research.microsoft.com/en-us/um/people/lamport/tla/book.html)：*Specifying Systems*是由TLA+的发明者Leslie Lamport编写的，并且仍然是关于TLA+的最全面的书。

