--------------------------- MODULE NS_protocol_2 ---------------------------

EXTENDS Naturals, FiniteSets

\* Множество идентификаторов агентов:
ID == { "a", "b", "p" }

\* Множество нонсов:
Nonces == { "Na", "Nb", "Np" }

\* Множество открытых ключей:
Pub_keys == { "pub_key_a",
              "pub_key_b",
              "pub_key_p" }

\* Множество закрытых ключей:
Priv_keys == { "priv_key_a",
               "priv_key_b",
               "priv_key_p" }

\* Множество всех ключей:
Keys == Pub_keys \cup Priv_keys

Keys_ == Keys \cup {"not_encrypted"}
\* not_encrypted - сообщение не зашифровано.

\* Множество ключей, доступных для агента "p":
p_AvailableKeys == Pub_keys \cup {"priv_key_p", "not_encrypted"}

\* Соответствие открытых и закрытых ключей:
pub_to_priv == [ pub_key_a |-> "priv_key_a",
                 pub_key_b |-> "priv_key_b",
                 pub_key_p |-> "priv_key_p" ]

\* Соответствие закрытых и открытых ключей:
priv_to_pub == [ priv_key \in Priv_keys |->
                 CHOOSE pub_key \in Pub_keys: pub_to_priv[pub_key] = priv_key ]

\* Соответствующий ключ для расшифровки:
decrypt_key == [ key \in Keys_ |->
                 CASE key \in Pub_keys  -> pub_to_priv[key]
                   [] key \in Priv_keys -> priv_to_pub[key]
                   [] OTHER             -> "not_encrypted"
               ]

\* Соответствие ID и открытых ключей:
id_to_pub == [ a |-> "pub_key_a",
               b |-> "pub_key_b",
               p |-> "pub_key_p" ]

\* Множество состояний агента "a".
StatesA == { "send_mes1", "wait_mes2", "send_mes3", "finalA" }

\* Следующее состояние агента "a".
next_a_state == [ send_mes1 |-> "wait_mes2",
                  wait_mes2 |-> "send_mes3",
                  send_mes3 |-> "finalA",
                  finalA    |-> "finalA" ]

\* Множество состояний агента "b".
StatesB == { "wait_mes1", "send_mes2", "wait_mes3", "finalB" }

\* Следующее состояние агента "b".
next_b_state == [ wait_mes1 |-> "send_mes2",
                  send_mes2 |-> "wait_mes3",
                  wait_mes3 |-> "finalB",
                  finalB    |-> "finalB" ]

\* Ссылки на узлы:
NodesRef == {"node2", "node3"}

\* Множество передаваемых (в протоколе) элементов данных:
DataItems == ID \cup Nonces \cup NodesRef \cup {"empty"}
\* empty - пустой элемент (означает отсутствие данных).

\* Номера элементов данных в сообщении:
ItemsNum == { "i1", "i2" }

\* Множество простых (не составных) сообщений:
SimpleMessages ==
    [ key  : Keys_,                     \* Ключ шифрования.
      item : [ItemsNum -> DataItems]    \* Элементы данных.
    ]

\* Множество передаваемых сообщений:
Messages == {<<mes>> : mes \in SimpleMessages} \cup
            (SimpleMessages \X SimpleMessages) \cup
            (SimpleMessages \X SimpleMessages \X SimpleMessages)

is_complex(mes) == \* Данное сообщение является составным.
    Cardinality(DOMAIN mes) > 1

\* Типы сообщений в протоколе:
MesTypes == { "mes1", "mes2", "mes3" }

\* Пустое незашифрованное сообщение:
empty_mes == <<[ key |-> "not_encrypted", item |-> [ i1 |-> "empty", i2 |-> "empty" ] ]>>

\**********************************************************************

VARIABLES
    p_input_mes,    \* Входящие сообщения агента "p".
    p_simple_mes,   \* Простые (входящие, разобранные на части) сообщения агента "p".
    p_Nonces,       \* Нонсы, которыми располагает агент "p".
    a_state,        \* Текущее состояние агента "a".
    b_state,        \* Текущее состояние агента "b".
    a_input_nonce,  \* Nonce, полученный агентом "a".
    b_input_nonce,  \* Nonce, полученный агентом "b".
    b_input_id,     \* ID, полученный агентом "b".
    a_connect_to,   \* Агент для связи, выбранный агентом "a".
    msg_type,       \* Тип сообщения (переменная для отладки).
    msg_kind,       \* Вид сообщения: созданное/существующее (переменная для отладки).
    sended_mes      \* Посланное сообщение (переменная для отладки).

vars == << p_input_mes, p_simple_mes, p_Nonces, a_state, b_state, a_input_nonce, b_input_nonce, b_input_id, a_connect_to, msg_type, msg_kind, sended_mes >>

(**************** SPECIFICATION **************)
Init ==
    /\ p_input_mes = {}
    /\ p_simple_mes = {}
    /\ p_Nonces = {"Np"}
    /\ a_state = "send_mes1"
    /\ b_state = "wait_mes1"
    /\ a_input_nonce = "empty"
    /\ b_input_nonce = "empty"
    /\ b_input_id = "empty"
    /\ a_connect_to \in (ID \ {"a"})
    /\ msg_type = "empty"
    /\ msg_kind = "empty"
    /\ sended_mes = empty_mes

\**********************************************************************
\*                               DECRYPT
\**********************************************************************
p_decrypt == \* Расшифровать сообщения.
    LET
        ComplexMes == \* Комплексные сообщения из "p_input_mes".
            { mes \in p_input_mes : is_complex(mes) }
        
        contains_mes(complex_mes, simple_mes) == \* Комплексное сообщение содержит простое сообщение.
            \E index \in (DOMAIN complex_mes):
                complex_mes[index] = simple_mes
        
        can_disassemble(mes) == \* Составное сообщение может быть разобрано.
            decrypt_key[mes[1].key] \in p_AvailableKeys
        
        ExtractedFromComplexMes == \* Множество простых сообщений, извлеченных из комплексных сообщений.
            { mes \in SimpleMessages:
                \E complex_mes \in ComplexMes:
                    /\ contains_mes(complex_mes, mes)
                    /\ can_disassemble(complex_mes) }
        
        NotComplexMes == \* Не комплексные сообщения из "p_input_mes".
            { mes \in p_input_mes : ~is_complex(mes) }
        
        ExtractedFromNotComplexMes == \* Множество простых сообщений, извлеченных из не комплексных сообщений.
            { mes[1] : mes \in NotComplexMes }
        
        ExtractedMes == \* Множество простых извлеченных из "p_input_mes" сообщений.
            ExtractedFromComplexMes \cup ExtractedFromNotComplexMes
        
        extract_simple_messages == \* Извлечь простые (SimpleMessages) сообщения из "p_input_mes".
            p_simple_mes' = p_simple_mes \cup ExtractedMes
        
        contains_item(mes, itm) == \* Простое сообщение содержит элемент данных.
            \E i \in ItemsNum: mes.item[i] = itm
        
        can_decrypt(mes) == \* Простое сообщение может быть расшифровано.
            decrypt_key[mes.key] \in p_AvailableKeys
        
        extracted_Nonces == \* Нонсы, полученные из извлеченных простых сообщений.
            { nonce \in Nonces:
                \E mes \in ExtractedMes:
                    /\ contains_item(mes, nonce)
                    /\ can_decrypt(mes) }
        
        extract_nonces_from_ExtractedMes == \* Извлечь нонсы из полученных простых сообщений.
            p_Nonces' = p_Nonces \cup extracted_Nonces
    IN
    /\ extract_simple_messages
    /\ extract_nonces_from_ExtractedMes
    /\ msg_type' = "empty"
    /\ msg_kind' = "empty"
    /\ sended_mes' = empty_mes
    /\ UNCHANGED << p_input_mes, a_state, b_state, a_input_nonce, b_input_nonce, b_input_id, a_connect_to >>

\**********************************************************************
\*                          MES_TRANSFER_P
\**********************************************************************
a_transfer_p == \* Передача сообщения от агента "a" к агенту "p".
    LET
        a_send == \* Агент "a" посылает сообщение.
            /\ a_state \in { "send_mes1", "send_mes3" }
            /\ a_state' = next_a_state[a_state]
        
        mes1 == <<  [ key |-> id_to_pub[a_connect_to], item |-> [ i1 |-> "node2", i2 |-> "empty" ] ],
                    [ key |-> "priv_key_a",            item |-> [ i1 |-> "Na",    i2 |-> "a"     ] ]
                >>
        
        mes3 == <<  [ key |-> id_to_pub[a_connect_to], item |-> [ i1 |-> "node2",       i2 |-> "empty" ] ],
                    [ key |-> "priv_key_a",            item |-> [ i1 |-> a_input_nonce, i2 |-> "empty" ] ]
                >>
        
        p_receive == \* Агент "p" получает сообщение.
            \/ /\ a_state = "send_mes1"
               /\ msg_type' = "mes1"
               /\ p_input_mes' = p_input_mes \cup {mes1}
               /\ sended_mes' = mes1
            
            \/ /\ a_state = "send_mes3"
               /\ msg_type' = "mes3"
               /\ p_input_mes' = p_input_mes \cup {mes3}
               /\ sended_mes' = mes3
    IN
    /\ a_send
    /\ p_receive
    /\ msg_kind' = "from_agent"
    /\ UNCHANGED << p_simple_mes, p_Nonces, b_state, a_input_nonce, b_input_nonce, b_input_id, a_connect_to >>

\**********************************************************************
b_transfer_p == \* Передача сообщения от агента "b" к агенту "p".
    LET
        b_send == \* Агент "b" посылает сообщение.
            /\ b_state = "send_mes2"
            /\ msg_type' = "mes2"
            /\ b_state' = next_b_state[b_state]
        
        mes2 == <<  [ key |-> id_to_pub[b_input_id], item |-> [ i1 |-> "node2",       i2 |-> "node3" ] ],
                    [ key |-> "not_encrypted",       item |-> [ i1 |-> b_input_nonce, i2 |-> "empty" ] ],
                    [ key |-> "priv_key_b",          item |-> [ i1 |-> "Nb",          i2 |-> "empty" ] ]
                >>
        
        p_receive == \* Агент "p" получает сообщение.
            /\ p_input_mes' = p_input_mes \cup {mes2}
            /\ sended_mes' = mes2
    IN
    /\ b_send
    /\ p_receive
    /\ msg_kind' = "from_agent"
    /\ UNCHANGED << p_simple_mes, p_Nonces, a_state, a_input_nonce, b_input_nonce, b_input_id, a_connect_to >>

\**********************************************************************
mes_transfer_p == \* Передача сообщения агенту "p".
    \/ a_transfer_p
    \/ b_transfer_p

\**********************************************************************
\*                          P_TRANSFER_MES
\**********************************************************************
AcceptedMessages1 == \* Множество принимаемых агентом "b" сообщений типа mes1.
    LET
        D1 == \* Множество допустимых значений параметра "закрытый_ключ".
            (Priv_keys \ {"priv_key_b"})
        
        id_for(priv_key) == \* Идентификатор, соответствующий данному закрытому ключу.
            CHOOSE id \in (ID \ {"b"}): id_to_pub[id] = decrypt_key[priv_key]
        
        D2 == \* Множество значений векторов <<закрытый_ключ, идентификатор_агента>>.
            { <<priv_key, id_for(priv_key)>> : priv_key \in D1 }
        
        D3 == \* Множество значений векторов <<(закрытый_ключ, идентификатор_агента), нонс>>.
            D2 \X (Nonces \ {"Nb"})
        
        Domain == \* Множество значений векторов <<закрытый_ключ, нонс, идентификатор_агента>>.
            { <<d[1][1], d[2], d[1][2]>> : d \in D3 }
                
        create_mes == \* Создать сообщение на основе вектора значений параметров.
            [ <<priv_key, nonce, id>> \in Domain |->
                    <<   [ key |-> "pub_key_b", item |-> [ i1 |-> "node2", i2 |-> "empty" ] ],
                         [ key |-> priv_key,    item |-> [ i1 |-> nonce,   i2 |-> id      ] ]
                    >>
            ]
    IN
    { create_mes[vec] : vec \in Domain }

\**********************************************************************
AcceptedMessages2 == \* Множество принимаемых агентом "a" сообщений типа mes2.
    LET
        Domain == (Nonces \ {"Na"})
        
        pub_key_for_decrypt == \* Открытый ключ, который будет использовать агент "a" для расшифровки вложенного сообщения.
            id_to_pub[a_connect_to]
        
        priv_key == CHOOSE key \in Priv_keys: decrypt_key[key] = pub_key_for_decrypt
                
        create_mes ==
            [ nonce \in Domain |->
                <<  [ key |-> "pub_key_a",     item |-> [ i1 |-> "node2", i2 |-> "node3" ] ],
                    [ key |-> "not_encrypted", item |-> [ i1 |-> "Na",    i2 |-> "empty" ] ],
                    [ key |-> priv_key,        item |-> [ i1 |-> nonce,   i2 |-> "empty" ] ]
                >>
            ]
    IN
    { create_mes[nonce] : nonce \in Domain }

\**********************************************************************
AcceptedMessages3 == \* Множество принимаемых агентом "b" сообщений типа mes3.
    LET
        pub_key_for_decrypt == \* Открытый ключ, который будет использовать агент "b" для расшифровки вложенного сообщения.
            id_to_pub[b_input_id]
        
        priv_key == CHOOSE key \in Priv_keys: decrypt_key[key] = pub_key_for_decrypt
    IN
    IF b_input_id # "empty" THEN
    {   
        <<  [ key |-> "pub_key_b", item |-> [ i1 |-> "node2", i2 |-> "empty" ] ],
            [ key |-> priv_key,    item |-> [ i1 |-> "Nb",    i2 |-> "empty" ] ]
        >>
    }
    ELSE {}

\**********************************************************************
AcceptedMessages(type) == \* Множество принимаемых агентами сообщений данного типа:
    CASE type = "mes1" -> AcceptedMessages1
      [] type = "mes2" -> AcceptedMessages2
      [] type = "mes3" -> AcceptedMessages3
      [] OTHER -> {}

\**********************************************************************
p_AvailableItems == \* Доступные агенту "p" элементы данных.
    (DataItems \ Nonces) \cup p_Nonces

\**********************************************************************
can_create_simple(mes) == \* Данное простое сообщение может быть создано агентом "p" из имеющихся данных.
    /\ mes \in SimpleMessages
    /\ mes.key \in p_AvailableKeys
    /\ mes.item["i1"] \in p_AvailableItems
    /\ mes.item["i2"] \in p_AvailableItems

\********************************************************************** 
can_create_transfer(mes) == \* Передаваемое сообщение может быть создано агентом "p" из имеющихся данных.
    /\ mes \in Messages
    /\ can_create_simple(mes[1])
    /\ \A i \in (DOMAIN mes) \ {1}:
            \/ can_create_simple(mes[i])
            \/ mes[i] \in p_simple_mes

\********************************************************************** 
p_send(mes) == \* Агент "p" посылает сообщение.
    LET
        send_existing == \* Агент "p" посылает существующее сообщение.
            /\ mes \in p_input_mes
            /\ msg_kind' = "existing"
        
        send_created == \* Агент "p" посылает созданное сообщение.
            /\ can_create_transfer(mes)
            /\ msg_kind' = "created"
    IN
    /\ \/ send_existing
       \/ send_created
    /\ sended_mes' = mes

\**********************************************************************
p_transfer_mes1 == \* Передача сообщения mes1 от агента "p" к агенту "b".
    LET
        b_receive(mes) == \* Агент "b" получает сообщение.
            /\ b_state        = "wait_mes1"
            /\ msg_type'      = "mes1"
            /\ b_input_nonce' = mes[2].item["i1"]
            /\ b_input_id'    = mes[2].item["i2"]
            /\ b_state'       = next_b_state[b_state]
    IN
    /\ \E mes \in AcceptedMessages("mes1"): /\ p_send(mes)
                                            /\ b_receive(mes)
    /\ UNCHANGED << p_input_mes, p_simple_mes, p_Nonces, a_state, a_input_nonce, a_connect_to >>

\**********************************************************************
p_transfer_mes2 == \* Передача сообщения mes2 от агента "p" к агенту "a".
    LET
        a_receive(mes) == \* Агент "a" получает сообщение.
            /\ a_state        = "wait_mes2"
            /\ msg_type'      = "mes2"
            /\ a_input_nonce' = mes[3].item["i1"]
            /\ a_state'       = next_a_state[a_state]
    IN
    /\ \E mes \in AcceptedMessages("mes2"): /\ p_send(mes)
                                            /\ a_receive(mes)
    /\ UNCHANGED << p_input_mes, p_simple_mes, p_Nonces, b_state, b_input_nonce, b_input_id, a_connect_to >>

\**********************************************************************
p_transfer_mes3 == \* Передача сообщения mes3 от агента "p" к агенту "b".
    LET
        b_receive(mes) == \* Агент "b" получает сообщение.
            /\ b_state   = "wait_mes3"
            /\ msg_type' = "mes3"
            /\ b_state'  = next_b_state[b_state]
    IN
    /\ \E mes \in AcceptedMessages("mes3"): /\ p_send(mes)
                                            /\ b_receive(mes)
    /\ UNCHANGED << p_input_mes, p_simple_mes, p_Nonces, a_state, a_input_nonce, b_input_nonce, b_input_id, a_connect_to >>

\**********************************************************************
p_transfer_mes == \* Передача сообщения от агента "p".
    \/ p_transfer_mes1
    \/ p_transfer_mes2
    \/ p_transfer_mes3

\**********************************************************************
Next ==
    \/ p_decrypt
    \/ mes_transfer_p
    \/ p_transfer_mes
    \/ UNCHANGED vars

(**************** INVARIANTS *****************)
TypeInv ==
    /\ p_input_mes \subseteq Messages
    /\ p_simple_mes \subseteq SimpleMessages
    /\ p_Nonces \subseteq Nonces
    /\ a_state \in StatesA
    /\ b_state \in StatesB
    /\ a_input_nonce \in Nonces \cup {"empty"}
    /\ b_input_nonce \in Nonces \cup {"empty"}
    /\ b_input_id \in ID \cup {"empty"}
    /\ a_connect_to \in (ID \ {"a"})
    /\ msg_type \in MesTypes \cup {"empty"}
    /\ msg_kind \in {"from_agent", "created", "existing", "empty"}
    /\ sended_mes \in Messages

authentication_completed == \* Агенты А и В завершили процесс аутентификации.
    /\ a_state = "finalA"
    /\ b_state = "finalB"

A_think_connected_B == \* Агент А считает, что взаимодействовал с агентом В.
    a_connect_to = "b"

B_think_connected_A == \* Агент В считает, что взаимодействовал с агентом А.
    b_input_id = "a"

AB_swap_nonces == \* Агенты А и В обменялись своими нонсами.
    /\ a_input_nonce = "Nb"
    /\ b_input_nonce = "Na"

AB_nonces_not_compromised == \* Нонсы агентов А и В не скомпрометированы.
    /\ "Na" \notin p_Nonces \* Нонс Na не известен злоумышленнику.
    /\ "Nb" \notin p_Nonces \* Нонс Nb не известен злоумышленнику.

\* Невозможна успешная аутентификация между агентами А и В. (not valid - возможна) 
Authentication_AB_not_successful ==
    LET Authentication_AB_successful ==
        /\ authentication_completed
        /\ A_think_connected_B
        /\ B_think_connected_A
        /\ AB_swap_nonces
        /\ AB_nonces_not_compromised
    IN ~Authentication_AB_successful

\* Безопасная аутентификация в направлении от А к В. (valid)
Secure_authentication_AB ==
    (authentication_completed /\ A_think_connected_B) =>
        /\ B_think_connected_A
        /\ AB_swap_nonces
        /\ AB_nonces_not_compromised

\* Безопасная аутентификация в направлении от В к А. (valid)
Secure_authentication_BA ==
    (authentication_completed /\ B_think_connected_A) =>
        /\ A_think_connected_B
        /\ AB_swap_nonces
        /\ AB_nonces_not_compromised

=============================================================================
