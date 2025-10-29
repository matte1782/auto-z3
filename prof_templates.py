# prof_templates.py
TEMPLATE_TAUTO = {
    "T1: (((p → q) → p) → p)": dict(vars=["p", "q"], parts=["Implies(Implies(Implies(p,q),p),p)"]),
    "T2: (p→(q∧r)) → ((p→q) ∧ (p→r))": dict(
        vars=["p", "q", "r"],
        parts=["Implies( Implies(p, And(q,r)), And(Implies(p,q),Implies(p,r)) )"],
    ),
}

TEMPLATE_EQUIV = {
    "E1: (p∨q→r) ≡ ((p→r)∧(q→r))": dict(
        vars=["p", "q", "r"],
        f1="Implies(Or(p,q), r)",
        f2="And(Implies(p,r), Implies(q,r))",
    ),
    "Circuiti (due reti)": dict(
        vars=["A", "B", "C"],
        f1="Or( And(Not(A),B,Not(C)), And(A,B,Not(C)), And(A,B,C) )",
        f2="Or( And(A,B), And(B,Not(C)) )",
    ),
}

TEMPLATE_INFER = {
    "I1: Classi di Peter": dict(
        vars=["PE", "PS", "PJ"],
        premises=["Xor(PE,PS)", "Implies(PS,PJ)", "Not(PJ)"],
        conclusion="PE",
    ),
    "I2: Mary/Lucia/Pioggia": dict(
        vars=["MG", "LG", "R"],
        premises=["Implies(LG,MG)", "Implies(R,Not(LG))"],
        conclusion="Implies(Not(R),MG)",
    ),
    "I3: Biglietto/Prenotazione": dict(
        vars=["FT", "MR"], premises=["Implies(FT,MR)", "Not(MR)"], conclusion="Not(FT)"
    ),
    "I4: Gruppo (Paul/Mary/John/Peter/Andrew)": dict(
        vars=["PaJ", "MJ", "JJ", "PeJ", "AJ"],
        premises=["Implies(PaJ, And(MJ,JJ))", "Implies(JJ, And(Not(PeJ),Not(AJ)))"],
        conclusion="Implies( Or(PeJ,AJ), Not(PaJ) )",
    ),
}

TEMPLATE_SAT = {
    "S1: (p→q) → ¬p": dict(
        vars=["p", "q"],
        asserts=["Implies(Implies(p,q), Not(p))"],
        get_model=True,
        scope=True,
    ),
    "S2: (p∨q)∧(p→q)∧(¬q∨p)∧¬(p∧q)": dict(
        vars=["p", "q"],
        asserts=["And( Or(p,q), Implies(p,q), Or(Not(q),p), Not(And(p,q)) )"],
        get_model=False,
        scope=True,
    ),
    "S3: (¬p∨¬q)∧(¬p∨r)∧(¬q∨r)": dict(
        vars=["p", "q", "r"],
        asserts=["And( Or(Not(p),Not(q)), Or(Not(p),r), Or(Not(q),r) )"],
        get_model=True,
        scope=False,
    ),
}

TEMPLATE_COLORING = {
    "America Centrale (K=3)": dict(
        K=3,
        nodes="Bel Gua ElS Hon Nic CR Pan",
        edges="Bel,Gua\nElS,Hon\nElS,Gua\nGua,Hon\nNic,Hon\nNic,CR\nNic,Pan",
    ),
    "Sud America (UNSAT con K=3)": dict(
        K=3,
        nodes=("Ven Col Ecu Per Guy Sur FGu Bra Bol Par Uru Arg Chi"),
        edges=(
            "\n".join(
                [
                    "Guy,Ven",
                    "Guy,Bra",
                    "Guy,Sur",
                    "Ven,Col",
                    "Ven,Bra",
                    "Bra,Sur",
                    "FGu,Sur",
                    "FGu,Bra",
                    "Col,Ecu",
                    "Col,Per",
                    "Col,Bra",
                    "Per,Ecu",
                    "Per,Bra",
                    "Per,Bol",
                    "Per,Chi",
                    "Bra,Bol",
                    "Par,Bol",
                    "Par,Arg",
                    "Arg,Bol",
                    "Chi,Bol",
                    "Bra,Arg",
                    "Bra,Par",
                    "Bra,Uru",
                    "Arg,Chi",
                    "Arg,Uru",
                ]
            )
        ),
    ),
}

TEMPLATE_XORn = {
    "ExactlyOne: a b c": dict(vars=["a", "b", "c"]),
    "ExactlyOne: x y z w": dict(vars=["x", "y", "z", "w"]),
}
