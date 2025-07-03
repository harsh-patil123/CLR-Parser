from re import *
from collections import OrderedDict

t_list=OrderedDict()
nt_list=OrderedDict()
production_list=[]


class Terminal:

    def __init__(self, symbol):
        self.symbol=symbol

    def __str__(self):
        return self.symbol


class NonTerminal:

    def __init__(self, symbol):
        self.symbol=symbol
        self.first=set()
        self.follow=set()

    def __str__(self):
        return self.symbol

    def add_first(self, symbols): self.first |= set(symbols) #union operation

    def add_follow(self, symbols): self.follow |= set(symbols)


def compute_first(symbol): 

    global production_list, nt_list, t_list

    if symbol in t_list:
        return set(symbol)

    for prod in production_list:
        head, body=prod.split('->')
        
        if head!=symbol: continue

        if body=='':
            nt_list[symbol].add_first(chr(1013))
            continue
        for i, Y in enumerate(body):
            if body[i]==symbol: continue
            t=compute_first(Y)
            nt_list[symbol].add_first(t-set(chr(1013)))
            if chr(1013) not in t:
                break 
            if i==len(body)-1: 
                nt_list[symbol].add_first(chr(1013))

    return nt_list[symbol].first

def get_first(symbol): #wrapper method for compute_first

    return compute_first(symbol)


def compute_follow(symbol):

    global production_list, nt_list, t_list

    if symbol == list(nt_list.keys())[0]: 
        nt_list[symbol].add_follow('$')

    for prod in production_list:    
        head, body=prod.split('->')

        for i, B in enumerate(body):        
            if B != symbol: continue

            if i != len(body)-1:
                nt_list[symbol].add_follow(get_first(body[i+1]) - set(chr(1013)))

            if i == len(body)-1 or chr(1013) in get_first(body[i+1]) and B != head: 
                nt_list[symbol].add_follow(get_follow(head))

def get_follow(symbol):

    global nt_list, t_list

    if symbol in t_list.keys():
        return None
    
    return nt_list[symbol].follow

def main(pl=None):

    print('''Enter the grammar productions (enter 'end' or return to stop)
#(Format: "A->Y1Y2..Yn" {Yi - single char} OR "A->" {epsilon})''')

    global production_list, t_list, nt_list
    ctr=1


    if pl==None:

        while True:

            
            production_list.append(input().replace(' ', ''))

            if production_list[-1].lower() in ['end', '']: 
                del production_list[-1]
                break

            head, body=production_list[ctr-1].split('->')

            if head not in nt_list.keys():
                nt_list[head]=NonTerminal(head)

            for i in body:
                if not 65<=ord(i)<=90:
                    if i not in t_list.keys(): t_list[i]=Terminal(i)
                elif  i not in nt_list.keys(): nt_list[i]=NonTerminal(i)
                
            ctr+=1
                
    return pl

if __name__=='__main__':
    
    main()