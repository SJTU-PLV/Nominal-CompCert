from itertools import groupby, chain

def process_group(g):
    g = [line[3:] for i, line in enumerate(g) if i == 0 or line != "##"]
    return g

def process(s):
    lines = s.split('\n')
    lines = [line for line in lines if line != "<YOUR SYNTAX ERROR MESSAGE HERE>"]
    groups = [list(g) for _, g in groupby(lines, lambda x: x[:2] == "##")]
    groups = [process_group(g) if g[0][:2] == "##" else g for g in groups]
    lines = chain(*groups)
    return "\n".join(lines)

if __name__ == "__main__":
    with open("RustsurfaceParserM.auto.messages") as f:
        s = f.read()
    s = process(s)
    with open("RustsurfaceParserM.messages", "w") as wf:
        wf.write(s)

