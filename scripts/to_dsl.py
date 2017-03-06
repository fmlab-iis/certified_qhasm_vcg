#!/usr/bin/env python

import sys
import re

class Instr:
  def __init__(self, asm, dsl):
    self.asm = asm
    self.dsl = dsl
  def to_string(self):
    return '(* ' + self.asm + ' *)\n' + self.dsl

def flatten(vs):
  return [num for elem in vs for num in elem]

def is_asm_comment(line):
  return re.match(r"^#.*$", line)

def is_empty_line(line):
  return re.match(r"^\s*$", line)

def trline(descriptor, line):
  substs, rules = descriptor
  res = line
  for lhs, rhs in substs.iteritems():
    res = res.replace(lhs, rhs)
  for pattern, replacement in rules.iteritems():
    if re.match(pattern, res):
      res = re.sub(pattern, replacement, res).strip()
      break
  return Instr(line, res)

def trfile(descriptor, fn):
  lines = []
  with open(fn) as f:
    lines = map(lambda line: trline(descriptor, line.strip()), [item for item in f.readlines() if not is_asm_comment(item) and not is_empty_line(item)])
  return lines

def parse_subst(line):
  tokens = map(lambda x: x.strip(), line.split("="))
  return (tokens[0], tokens[1])

def parse_rule(line):
  nums = [1, 2, 3, 4]
  tokens = map(lambda x: x.strip(), line.split("->"))
  pairs = [(tokens[0], tokens[1])]
  tmp = []
  for i in nums:
    for pattern, replacement in pairs:
      if pattern.find("$" + str(i) + "c") != -1:
        pc = pattern.replace("$" + str(i) + "c", "\\$(?P<w" + str(i) + ">\\d+)", 1)
        pc = pc.replace("$" + str(i) + "c", "\\$(?P=w" + str(i) + ")")
        rc = replacement.replace("$" + str(i) + "c", "\\" + str(i) + "")
        tmp.append((pc, rc))
      elif pattern.find("$" + str(i) + "v") != -1:
        pv = pattern.replace("$" + str(i) + "v", "%%(?P<w" + str(i) + ">[a-zA-Z]\\w*)", 1)
        pv = pv.replace("$" + str(i) + "v", "%%(?P=w" + str(i) + ")")
        rv = replacement.replace("$" + str(i) + "v", "\\" + str(i) + "")
        tmp.append((pv, rv))
      else:
        tmp.append((pattern, replacement))
    pairs = tmp
    tmp = []
  pairs = [(re.sub(r"\s+", "\\s*", pattern), replacement) for (pattern, replacement) in pairs]
  return pairs

def parse_pattern(line):
  substs = []
  rules = []
  if line.find("->") == -1:
    substs.append(parse_subst(line))
  else:
    rules = rules + parse_rule(line)
  return (substs, rules)

def parse_descriptor(fn):
  substs = []
  rules = []
  with open(fn) as f:
    lines = map(parse_pattern, [item for item in f.readlines() if not is_asm_comment(item) and not is_empty_line(item)])
    substs = substs + [x[0] for x in lines]
    rules = rules + [x[1] for x in lines]
  return (dict(flatten(substs)), dict(flatten(rules)))

def vars(instrs):
  vars = set()
  for instr in instrs:
    m = re.search(r"zAssign\s+(\w+)\s+.*|\zSplit\s+(\w+)\s+(\w+)\s+.*|(\w+)\s*@:=.*", instr.dsl)
    if (m != None):
      for v in [v for v in m.groups() if v != None]:
        vars.add(v)
    m = re.findall(r"zVar\s+(\w+)|zVar\s*\((\w+)\)", instr.dsl)
    for vs in m:
      for v in [v for v in vs if v != ""]:
        vars.add(v)
  return vars

def main():
  if len(sys.argv) == 3:
    res = trfile(parse_descriptor(sys.argv[1]), sys.argv[2])
    print "From Coq Require Import ZArith ."
    print "From mQhasm Require Import zDSL zRadix ."
    print "From mathcomp Require Import seq ."
    print "Open Scope N_scope."
    print "Open Scope zdsl_scope."
    print "Definition program :="
    i = 0
    for v in vars(res):
      print ("let " + v + " := " + str(i) + " in")
      i = i + 1
    print "[::"
    print ("\n".join(map((lambda i: i.to_string() + ";"), res[0:len(res)-1])) +
           "\n" +
           res[len(res)-1].to_string())
    print "]."
  else:
    print "Wrong number of arguments."
    print "Usage: python " + sys.argv[0] + " DESCRIPTOR ASSEMBLY"

if __name__ == "__main__":
  main()
