from collections import deque
from collections import OrderedDict
import firstfollow
from firstfollow import production_list, nt_list as ntl, t_list as tl

nt_list, t_list = [], []

class State:
    _id = 0
    def __init__(self, closure):
        self.closure = closure
        self.no = State._id
        State._id += 1

class Item(str):
    def __new__(cls, item, lookahead=list()):
        self = str.__new__(cls, item)
        self.lookahead = lookahead
        return self

    def __str__(self):
        return super(Item, self).__str__() + ", " + '|'.join(self.lookahead)

def closure(items):
    def exists(newitem, items):
        for i in items:
            if i == newitem and sorted(set(i.lookahead)) == sorted(set(newitem.lookahead)):
                return True
        return False

    global production_list

    while True:
        flag = 0
        for i in items:
            if i.index('.') == len(i) - 1:
                continue

            Y = i.split('->')[1].split('.')[1][0]

            if i.index('.') + 1 < len(i) - 1:
                lastr = list(firstfollow.compute_first(i[i.index('.') + 2]) - set(chr(1013)))
            else:
                lastr = i.lookahead

            for prod in production_list:
                head, body = prod.split('->')
                if head != Y:
                    continue
                newitem = Item(Y + '->.' + body, lastr)
                if not exists(newitem, items):
                    items.append(newitem)
                    flag = 1
        if flag == 0:
            break

    return items

def goto(items, symbol):
    global production_list
    initial = []
    for i in items:
        if i.index('.') == len(i) - 1:
            continue

        head, body = i.split('->')
        seen, unseen = body.split('.')

        if unseen[0] == symbol and len(unseen) >= 1:
            initial.append(Item(head + '->' + seen + unseen[0] + '.' + unseen[1:], i.lookahead))

    return closure(initial)

def calc_states():
    def contains(states, t):
        for s in states:
            if len(s) != len(t):
                continue
            if sorted(s) == sorted(t):
                for i in range(len(s)):
                    if s[i].lookahead != t[i].lookahead:
                        break
                else:
                    return True
        return False

    global production_list, nt_list, t_list

    head, body = production_list[0].split('->')
    states = [closure([Item(head + '->.' + body, ['$'])])]

    while True:
        flag = 0
        for s in states:
            for e in nt_list + t_list:
                t = goto(s, e)
                if t == [] or contains(states, t):
                    continue
                states.append(t)
                flag = 1
        if not flag:
            break

    return states

def make_table(states):
    global nt_list, t_list

    def getstateno(t):
        for s in states:
            if len(s.closure) != len(t):
                continue
            if sorted(s.closure) == sorted(t):
                for i in range(len(s.closure)):
                    if s.closure[i].lookahead != t[i].lookahead:
                        break
                else:
                    return s.no
        return -1

    def getprodno(closure):
        closure = ''.join(closure).replace('.', '')
        return production_list.index(closure)

    SLR_Table = OrderedDict()

    for i in range(len(states)):
        states[i] = State(states[i])

    for s in states:
        SLR_Table[s.no] = OrderedDict()

        for item in s.closure:
            head, body = item.split('->')
            if body == '.':
                for term in item.lookahead:
                    SLR_Table[s.no].setdefault(term, set()).add('r' + str(getprodno(item)))
                continue

            nextsym = body.split('.')[1]
            if nextsym == '':
                if getprodno(item) == 0:
                    SLR_Table[s.no]['$'] = 'ac'
                else:
                    for term in item.lookahead:
                        SLR_Table[s.no].setdefault(term, set()).add('r' + str(getprodno(item)))
                continue

            nextsym = nextsym[0]
            t = goto(s.closure, nextsym)
            if t != []:
                if nextsym in t_list:
                    SLR_Table[s.no].setdefault(nextsym, set()).add('s' + str(getstateno(t)))
                else:
                    SLR_Table[s.no][nextsym] = str(getstateno(t))

    return SLR_Table

def augment_grammar():
    for i in range(ord('Z'), ord('A') - 1, -1):
        if chr(i) not in nt_list:
            start_prod = production_list[0]
            production_list.insert(0, chr(i) + '->' + start_prod.split('->')[0])
            return

# NEW: Load table from file
def parse_table_file(filename="table.txt"):
    table = {}
    with open(filename, 'r') as file:
        lines = [line.strip() for line in file.readlines()]
    i = 0
    while i < len(lines):
        if lines[i].isdigit():
            state = int(lines[i])
            table[state] = {}
            i += 1
            while i < len(lines) and not lines[i].isdigit():
                parts = lines[i].split()
                symbol = parts[0]
                actions = parts[1:]
                table[state][symbol] = set(actions)
                i += 1
        else:
            i += 1
    return table


def parse_string(input_string, parsing_table, productions):
    """Parse the input string and print the LR parsing trace.

    The trace now starts with an **empty stack** (only the initial state 0)
    and the **full untouched input**. This gives a clearer, textbook-style
    view of how the parser proceeds step‑by‑step.
    """

    input_string += '$'
    stack = [0]          # LR parsing stack – starts with state 0 only
    pointer = 0          # Points to the current symbol in the input

    # ── Pretty‑print table header ──────────────────────────────────────────
    print(f"\nParsing input: {input_string}")
    print(f"{'Stack':<30} {'Input':<20} Action")
    print('-'*60)

    # 🔹 INITIAL configuration (empty stack / full input)
    print(f"{str(stack):<30} {input_string[pointer:]:<20}  ––– start–––")

    # ── Main LR parsing loop ──────────────────────────────────────────────
    while True:
        state = stack[-1]
        current_symbol = input_string[pointer]

        action = parsing_table.get(state, {}).get(current_symbol)

        if action is None:
            print(f"{str(stack):<30} {input_string[pointer:]:<20} ERROR: Unexpected symbol '{current_symbol}'")
            return False

        # If multiple actions are stored as a set, pick the (only) element
        action = list(action)[0] if isinstance(action, set) else action

        # ── SHIFT ─────────────────────────────────────────────────────────
        if action.startswith('s'):
            next_state = int(action[1:])
            stack.append(current_symbol)
            stack.append(next_state)
            pointer += 1
            print(f"{str(stack):<30} {input_string[pointer:]:<20} Shift and go to state {next_state}")

        # ── REDUCE ────────────────────────────────────────────────────────
        elif action.startswith('r'):
            prod_index = int(action[1:])
            prod = productions[prod_index]
            lhs, rhs = prod.split('->')

            # Pop |rhs|*2 items (symbol & state alternately) – but only if rhs≠ε
            if rhs != '':
                pop_len = len(rhs) * 2
                stack = stack[:-pop_len]

            # GOTO after reduction
            top_state = stack[-1]
            stack.append(lhs)
            goto_action = parsing_table.get(top_state, {}).get(lhs)
            if goto_action is None:
                print(f"{str(stack):<30} {input_string[pointer:]:<20} ERROR: No GOTO for {lhs}")
                return False
            next_state = int(goto_action) if isinstance(goto_action, str) else int(list(goto_action)[0])
            stack.append(next_state)
            print(f"{str(stack):<30} {input_string[pointer:]:<20} Reduce using {prod}, GOTO {next_state}")

        # ── ACCEPT ────────────────────────────────────────────────────────
        elif action == 'ac':
            print(f"{str(stack):<30} {input_string[pointer:]:<20} ACCEPT")
            return True

        # ── UNKNOWN / INVALID ACTION ─────────────────────────────────────
        else:
            print(f"{str(stack):<30} {input_string[pointer:]:<20} ERROR: Invalid action {action}")
            return False


def main():
    global production_list, ntl, nt_list, tl, t_list

    # Collect grammar and compute FIRST/FOLLOW
    firstfollow.main()

    print("\tFIRST AND FOLLOW OF NON-TERMINALS")
    for nt in ntl:
        firstfollow.compute_first(nt)
        firstfollow.compute_follow(nt)
        print(nt)
        print("\tFirst:\t", firstfollow.get_first(nt))
        print("\tFollow:\t", firstfollow.get_follow(nt), "\n")

    augment_grammar()
    nt_list = list(ntl.keys())
    t_list = list(tl.keys()) + ['$']

    # Build CLR(1) item sets & table
    states = calc_states()

    # Dump items
    with open('items.txt', 'w') as output:
        for idx, s in enumerate(states):
            output.write(str(idx) + '\n')
            for itm in s:
                output.write(itm + '\n')

    table = make_table(states)

    # Dump table for later use / inspection
    with open("table.txt", "w") as output:
        for i in table:
            output.write(str(i) + '\n')
            for j in table[i]:
                output.write(str(j) + " ")
                for k in table[i][j]:
                    output.write(str(k))
                output.write('\n')

    # Pretty‑print table summary
    print('_______________________________________________________________________________________')
    print("\n\tCLR(1) TABLE\n")
    sym_list = nt_list + t_list
    print('_______________________________________________________________________________________')
    print('\t|  ', '\t|  '.join(sym_list), '\t\t|')
    print('_______________________________________________________________________________________')
    for i, row in table.items():
        print(i, "\t|  ", '\t|  '.join(list(row.get(sym, ' ') if isinstance(row.get(sym), str) or row.get(sym) is None else next(iter(row.get(sym, ' '))) for sym in sym_list)), '\t\t|')
    print('_______________________________________________________________________________________')

    # Interactive parse loop
    table_dict = parse_table_file("table.txt")
    while True:
        test_input = input("\nEnter a string to parse (or type 'exit' to quit): ").strip()
        if test_input.lower() == 'exit':
            break
        result = parse_string(test_input, table_dict, production_list)
        print("Result:", "Accepted" if result else "Rejected")


if __name__ == "__main__":
    main()
