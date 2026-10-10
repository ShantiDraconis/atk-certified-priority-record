#!/usr/bin/env python3
"""Copy Lean snapshots from eight source repositories, fail closed on mismatch."""
import hashlib,json,os,pathlib,subprocess,tempfile
ROOT=pathlib.Path.cwd()
REPOS=["Elyon-Public-Proof","m-core-riemann","m-core-p-vs-np","m-core-yang-mills","navier-stokes-critical-barrier-audit","m-core-bsd","m-core-hodge","m-core-beal"]
def run(*args,cwd=None,env=None):
    return subprocess.check_output(args,cwd=cwd,env=env).decode().strip()
def main():
    records=[]
    provenance=ROOT/"provenance"
    provenance.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="atk-source-") as temp:
        base=pathlib.Path(temp)
        for repo in REPOS:
            source=base/repo
            env=os.environ.copy()
            token=env.get("GH_READ_TOKEN","")
            if token:
                askpass=base/"askpass.sh"
                askpass.write_text('#!/bin/sh\ncase "$1" in *Username*) echo x-access-token;; *) printf "%s\\n" "$GH_READ_TOKEN";; esac\n')
                askpass.chmod(0o700)
                env["GIT_ASKPASS"]=str(askpass)
            env["GIT_TERMINAL_PROMPT"]="0"
            try:
                subprocess.run(["git","clone","--quiet","https://github.com/ShantiDraconis/"+repo+".git",str(source)],check=True,env=env)
                before=run("git","rev-parse","HEAD",cwd=source)
                status_before=run("git","status","--porcelain",cwd=source)
                if status_before: raise RuntimeError("Dirty source checkout")
                files=run("git","ls-files","-z",cwd=source).split("\0")
                for path in files:
                    if not path.endswith(".lean"): continue
                    relative=pathlib.PurePosixPath(path)
                    if ".." in relative.parts: raise RuntimeError("Unsafe path")
                    src=source/path
                    if src.is_symlink() or not src.is_file(): raise RuntimeError("Unsupported source")
                    data=src.read_bytes()
                    blob=run("git","hash-object","--",path,cwd=source)
                    target=ROOT/"snapshots"/repo/path
                    target.parent.mkdir(parents=True,exist_ok=True)
                    if target.exists() and target.read_bytes()!=data: raise RuntimeError("Existing snapshot differs: "+str(target))
                    if not target.exists(): target.write_bytes(data)
                    copied=run("git","hash-object","--",str(target),cwd=ROOT)
                    if blob!=copied: raise RuntimeError("Blob mismatch")
                    records.append({"repository":repo,"path":path,"source_commit":before,"git_blob_sha1":blob,"sha256":hashlib.sha256(data).hexdigest()})
                after=run("git","rev-parse","HEAD",cwd=source)
                status_after=run("git","status","--porcelain",cwd=source)
                if before!=after or status_after: raise RuntimeError("Source modified")
                (provenance/(repo+"_SOURCE_BEFORE_AFTER.json")).write_text(json.dumps({"before":before,"after":after,"status_before":status_before,"status_after":status_after},indent=2)+"\n")
            except Exception as e:
                (provenance/"ATK_COPY_FAILURE.json").write_text(json.dumps({"repository":repo,"status":"BLOCKED_BY_CONNECTION_OR_VERIFICATION","error":str(e)},indent=2)+"\n")
                raise
    records.sort(key=lambda x:(x["repository"],x["path"]))
    (provenance/"ATK_COPY_MANIFEST.json").write_text(json.dumps({"scope":"Lean provenance only","mathematical_certification":False,"files":records},indent=2)+"\n")
    (provenance/"SHA256SUMS").write_text("".join(f'{r["sha256"]}  snapshots/{r["repository"]}/{r["path"]}\n' for r in records))
    (provenance/"ATK_COPY_SUMMARY.json").write_text(json.dumps({"verified_files":len(records),"historical_reference":789,"complete_against_historical_reference":len(records)==789,"mathematical_certification":False},indent=2)+"\n")
    print("Verified Lean snapshots:",len(records))
if __name__=="__main__": main()
