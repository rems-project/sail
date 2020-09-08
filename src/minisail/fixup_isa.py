import tempfile, os, shutil,sys

skip=False


for filename in sys.argv[1:]:

    with tempfile.NamedTemporaryFile(delete=False) as temp_file:

        temp_file.write("open Ast\n")
        temp_file.write("open Type_check\nopen Utils2\n")
        
        with open(filename) as infile:

            for line in infile:

                if line.startswith("module Ast : sig"):
                    print ("Start skipping..")
                    skip=True

                # We couldn't use typ in ISabelle and have to use typp.
                line = line.replace("typp","typ")
                #line = line.replace("(unit Env.env_ext * Ast.typ)","Type_check.tannot")
                

                #line = line.replace("Env.getTyp", "Utils2.getTyp")
                #line = line.replace("Env.lookup_id", "Utils2.lookup_id")
                
                line = line.replace("unit Env.env_ext" , "Type_check.env")
                #line = line.replace("('a * Ast.typ)" , "Type_checker.tannot")
                line = line.replace("(unit Env.tannot_ext option)", "Type_check.tannot")
                line = line.replace("Arith.equal_int num numa" , "num = numa")
                line = line.replace("Ast.Unknown", "Parse_ast.Unknown")
                line = line.replace("Arith.equal_inta c ca", "c = ca")
                line = line.replace("Arith.equal_int c ca", "c = ca")

                line = line.replace("Arith.equal_inta num numa","(num = numa)")
                line = line.replace("Arith.equal_int xaa", "xaa =")
                line = line.replace("Ast.equal_order", "Utils2.equal_order")
                line = line.replace("Ast.equal_typa", "Utils2.equal_typa")
                
                # This is because type_synonym for this wasn't coming out of sail.ott
                line = line.replace("Ast.PEXP_funcl pexp", "pexp")
                
                # Must be last
                line = line.replace("Env.", "Utils2.")
                
                for s in [ "  val getEnv", "  val getType",
                           "let rec getEnv", "let rec getType" ]:
                    if line.startswith(s):
                        line = ""
                        break
                    
                
                if not skip:
                    temp_file.write(line)

                if line.startswith("end;; (*struct Env*)"):
                    print ("End skip")
                    skip=False
                    
        shutil.move(temp_file.name, filename)

