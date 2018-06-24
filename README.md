# 介绍

## 什么是TLA+

```
People == {"alice", "bob"}
Items == {"ore", "sheep", "brick"}
(* --algorithm trade
variable owner_of \in [Items -
>
 People]

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



