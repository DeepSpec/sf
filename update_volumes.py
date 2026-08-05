#!/usr/bin/env python3
import os
import sys
import re
import json
import urllib.request
import tarfile
import shutil

VOLUMES = ["lf", "plf", "vfa", "qc", "vc", "slf", "secf"]

VOL_URLS = {
    "lf": "https://softwarefoundations.cis.upenn.edu/lf-current/index.html",
    "plf": "https://softwarefoundations.cis.upenn.edu/plf-current/index.html",
    "vfa": "https://softwarefoundations.cis.upenn.edu/vfa-current/index.html",
    "qc": "https://softwarefoundations.cis.upenn.edu/qc-current/index.html",
    "vc": "https://softwarefoundations.cis.upenn.edu/vc-current/index.html",
    "slf": "https://softwarefoundations.cis.upenn.edu/slf-current/index.html",
    "secf": "https://softwarefoundations.cis.upenn.edu/secf-current/index.html"
}

STATE_FILE = "versions.json"

def fetch_version_string(url):
    try:
        req = urllib.request.Request(
            url, 
            headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
        )
        with urllib.request.urlopen(req) as response:
            html = response.read().decode('utf-8', errors='ignore')
        
        # Try BeautifulSoup if available
        try:
            from bs4 import BeautifulSoup
            soup = BeautifulSoup(html, 'html.parser')
            for elem in soup.find_all(string=re.compile(r'[Vv]ersion\s+\d+\.\d+', re.I)):
                text = elem.strip()
                if text.lower().startswith('version'):
                    return re.sub(r'\s+', ' ', text)
        except Exception:
            pass

        # Regex fallback
        match = re.search(r'[Vv]ersion\s+\d+\.\d+[^<\n]*', html)
        if match:
            ver_str = match.group(0).strip()
            ver_str = re.sub(r'<[^>]*>', '', ver_str)
            ver_str = re.sub(r'\s+', ' ', ver_str)
            return ver_str
    except Exception as e:
        print(f"Error fetching version from {url}: {e}")
    return None

def update_volume(vol):
    dest_dir = f"{vol}-current"
    tgz_url = f"https://softwarefoundations.cis.upenn.edu/{vol}-current/{vol}.tgz"
    tgz_path = f"/tmp/{vol}.tgz"
    
    print(f"Downloading {tgz_url} to {tgz_path}...")
    req = urllib.request.Request(
        tgz_url,
        headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
    )
    with urllib.request.urlopen(req) as response, open(tgz_path, 'wb') as out_file:
        shutil.copyfileobj(response, out_file)
        
    # Clear existing destination directory completely if it exists
    if os.path.exists(dest_dir):
        print(f"Removing existing directory {dest_dir} completely...")
        shutil.rmtree(dest_dir)
        
    # Unpack tarball into current directory
    print(f"Unpacking {tgz_path}...")
    with tarfile.open(tgz_path, 'r:gz') as tar:
        try:
            tar.extractall(path=".", filter="data")
        except TypeError:
            tar.extractall(path=".")
        
    # Tarball unpacks into e.g. "lf/". Rename/move "lf" to "lf-current"
    unpacked_dir = vol
    if os.path.exists(unpacked_dir):
        print(f"Renaming {unpacked_dir} to {dest_dir}...")
        os.rename(unpacked_dir, dest_dir)
    else:
        print(f"Warning: Expected unpacked directory '{unpacked_dir}' was not found.")
        
    # Remove downloaded tarball from /tmp
    if os.path.exists(tgz_path):
        os.remove(tgz_path)
        
    # Ensure tar file inside destination directory is removed
    in_dir_tgz = os.path.join(dest_dir, f"{vol}.tgz")
    if os.path.exists(in_dir_tgz):
        print(f"Removing tar file from inside {dest_dir} ({in_dir_tgz})...")
        os.remove(in_dir_tgz)

def main():
    args = sys.argv[1:]
    force = False
    if "--force" in args:
        force = True
        args.remove("--force")
        
    target_vols = VOLUMES
    if args:
        filtered_args = [a.lower() for a in args if a.lower() in VOLUMES]
        if filtered_args:
            target_vols = filtered_args
        else:
            print(f"Usage: python3 update_volumes.py [--force] [volume_name...]")
            print(f"Available volumes: {VOLUMES}")
            sys.exit(1)

    state = {}
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, 'r', encoding='utf-8') as f:
                state = json.load(f)
        except Exception as e:
            print(f"Error loading state file {STATE_FILE}: {e}")

    updated_any = False

    for vol in target_vols:
        print(f"\n--- Checking volume: {vol} ---")
        url = VOL_URLS[vol]
        remote_version = fetch_version_string(url)
        if not remote_version:
            print(f"Could not retrieve remote version for {vol}. Skipping.")
            continue

        stored_version = state.get(vol)
        dest_dir = f"{vol}-current"
        dir_exists = os.path.exists(dest_dir)
        in_dir_tgz = os.path.join(dest_dir, f"{vol}.tgz")

        needs_update = (stored_version != remote_version) or (not dir_exists) or force

        print(f"Stored version:  '{stored_version}'")
        print(f"Remote version:  '{remote_version}'")
        print(f"Needs update:    {needs_update}")

        if needs_update:
            try:
                update_volume(vol)
                state[vol] = remote_version
                updated_any = True
                print(f"Volume {vol} successfully updated to '{remote_version}'!")
            except Exception as e:
                print(f"Failed to update volume {vol}: {e}")
        else:
            if os.path.exists(in_dir_tgz):
                print(f"Cleaning up lingering tar file inside {dest_dir}...")
                os.remove(in_dir_tgz)
                updated_any = True
            print(f"Volume {vol} is already up to date.")

    if updated_any or not os.path.exists(STATE_FILE):
        with open(STATE_FILE, 'w', encoding='utf-8') as f:
            json.dump(state, f, indent=2, ensure_ascii=False)
            f.write("\n")
        print("\nUpdated versions.json state file successfully.")
    else:
        print("\nAll volumes are in sync.")

if __name__ == "__main__":
    main()
