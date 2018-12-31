# 软件分析第二次大作业

### 算法概述

设计了一个较为高效的 Example Based Synthesis 算法，具有如下的特点：

1. 效率高，可以在时间限制能正确生成本次大作业 open_tests 中的**所有**测试用例。

2. 结果简洁，可以生成 “极简” 的程序，下面是本算法生成的两个例子：

   ```scheme
   (define-fun max6 ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int)) Int (ite (and (and (and (and (<= x2 x1) (<= x3 x1)) (<= x4 x1)) (<= x5 x1)) (<= x6 x1)) x1 (ite (and (and (and (<= x3 x2) (<= x4 x2)) (<= x5 x2)) (<= x6 x2)) x2 (ite (and (and (<= x4 x3) (<= x5 x3)) (<= x6 x3)) x3 (ite (and (<= x5 x4) (<= x6 x4)) x4 (ite (<= x6 x5) x5 x6))))))
   ```

   ```scheme
   (define-fun findIdx ((y1 Int) (y2 Int) (y3 Int) (k1 Int)) Int (ite (or (or (or (or (<= y2 y1) (<= y3 y2)) (<= k1 y1)) (= y3 k1)) (= y2 k1)) 0 (ite (<= k1 y2) 1 (ite (<= k1 y3) 2 3))))
   ```

   其中第一个程序是 `max6` 的答案，第二个程序是 `array_search_3`。值得注意的是，在 `array_serach_3` 中，并没有对序列无序或者 $k1$ 和数列中某一个元素值相同的情况进行约束，可以发现在我们的算法把这个约束准确地求出了。


### 算法过程

算法主要分成三部分：

1. 求出可能作为返回值的表达式集合（不含 `ite`） $R$。
2. 求出可能出现在 if 条件里的比较表达式（形如 $x \leq, <, = y$）集合 $C$。
3. 对 $R$ 中的每一个元素生成一个它作为返回值的条件（以析取范式的形式）。

目前本算法只能处理在输入中，所有输入均以 $(f\ x\ y\ z)$ 形式出现的情况。因此在读入输入的时候，算法会先尝试把所有 $f$ 的调用变换成相同的形式，碰到不能变换的情况（例如一个等号两端出现了参数不同的两次调用）会转而用更加暴力的方法求解。

这儿定义 $\phi(t)$ 为把输入约束中的所有 $(f\ x\ y\ z)$ 都替换成表达式 $t$ 后的约束。

#### 第一部分

可以判断一个表达式集合 $R$ 是否覆盖了 $f$ 的所有返回值，即下列布尔表达式不可满足：
$$
\neg (\phi(\text{value}) \wedge \bigvee_{t \in R} [\text{value} = t])
$$
因为在测试集中，返回值的形式都非常简单，因此这儿使用最暴力的方法，令 $R(k)$ 为包含 $k$ 个运算符（不含 `ite`）的所有表达式集合，直接找到最小的 $k$ 使得 $R(k)$ 满足条件。

因为这样找到的 $R(k)$ 非常大，因此使用了简单的二分来去重，找到一个极小的满足条件集合作为 $R$ 返回。因为在 `Int` 范围内，很难出现两个不同的表达式集合 $A,B$ 对应的取值集合是完全相同的情况，因此该算法能非常精确的找到 $R$。

当返回值形式比较复杂的时候，也可以用一个 example based synthesis 来生成表达式（每次找到一个反例再生成一个表达式覆盖它）。

#### 第二部分

因为测试集中，条件判断的形式都非常简单，因此这儿令 $C(k)$ 为包含 $k$ 个运算符的比较表达式。从小到大依次尝试用 $C(k)$ 进行生成，直到正确的生成出程序为止。

#### 第三部分

我们以析取范式的形式来生成答案，即对每一个返回值，生成一系列的集合 $P_i \subseteq C$，对应的布尔表达式为: $\bigvee_{P_i} \bigwedge_{t \in P_i} t$.

设 $R$ 中的元素为 $t_1$ 至 $t_n$，当前正在生成 $t$
