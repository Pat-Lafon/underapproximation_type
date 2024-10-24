import sys
import argparse
import os
import subprocess
import shutil
import locale
import run_bench
import re

cmd_prefix = ["dune", "exec", "--", "bin/main.exe"]
config_file = "meta-config.json"
workdir = ""
verbose = True

def run_type_infer_aux(meta_config_file, f):
    cmd = cmd_prefix + ["type-infer", meta_config_file, f]
    run_bench.invoc_cmd(verbose, cmd, None)

def run_type_infer(dir_str):
    meta_config_file = "{}/{}".format(dir_str, config_file)
    if not (os.path.exists(meta_config_file)):
        for f in os.listdir(dir_str):
            pp = "{}/{}".format(dir_str, f)
            if os.path.isdir(pp):
                run_type_infer(pp)
    else:
        print(dir_str)
        files = os.listdir(dir_str)
        # files.reverse()
        for filename in files:
            matches = re.search(r"prog[0-9]+\.ml$", filename, re.MULTILINE)
            if matches:
                run_type_infer_aux(meta_config_file, "{}/{}".format(dir_str, filename))

if __name__ == '__main__':
    dir_str = sys.argv[1]
    run_type_infer(dir_str)
