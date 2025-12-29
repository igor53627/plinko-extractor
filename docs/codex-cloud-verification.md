# Codex Cloud + Remote Rocq Verification

This document describes how to use Codex Cloud for automated Coq/Rocq proof synthesis with remote verification.

## Architecture

```
+------------------+     HTTP POST      +----------------------+
|  Codex Cloud     | -----------------> |  Verification Server |
|  (gpt-5.2-codex) |                    |  108.61.166.134:80   |
+------------------+                    +----------------------+
        |                                        |
        | synthesize proof                       | rocq compile
        v                                        v
+------------------+                    +----------------------+
|  Return diff     | <----------------- |  {"success": true}   |
+------------------+     JSON response  +----------------------+
```

## Server Setup (108.61.166.134)

### Components

1. **rocq-verify.service** - Python HTTP API on port 8847
2. **nginx** - Reverse proxy on port 80 (Codex Cloud only allows port 80)
3. **Rocq Prover 9.1.0** - Installed via opam for coq-api user

### API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/health` | GET | Health check, returns `{"status": "ok", "rocq_version": "9.1.0"}` |
| `/verify` | POST | Single file verification |
| `/verify-project` | POST | Multi-file project verification |

### /verify-project Request Format

```json
{
  "files": {
    "Plinko/Specs/CommonTypes.v": "...",
    "Plinko/Specs/SwapOrNotSpec.v": "...",
    "Plinko/Specs/SwapOrNotSrSpec.v": "..."
  },
  "main": "Plinko/Specs/SwapOrNotSrSpec.v",
  "timeout": 120
}
```

### Response Format

```json
{
  "success": true,
  "returncode": 0,
  "stdout": "",
  "stderr": "",
  "admitted": true
}
```

## Usage

### Submit a Proof Task

```bash
codex cloud exec --env 694e8588110c8191945f9b9dfbf0b7d1 --attempts 3 "
Prove \`lemma_name\` in plinko/formal/specs/SomeSpec.v

The lemma:
\`\`\`coq
Lemma lemma_name : forall x, ...
\`\`\`

Verify using:
curl -s -X POST http://108.61.166.134/verify-project \\
  -H 'Content-Type: application/json' \\
  -d '{\"files\": {...}, \"main\": \"Plinko/Specs/SomeSpec.v\", \"timeout\": 120}'

Read .v files from plinko/formal/specs/, key as Plinko/Specs/<name>.v.
Iterate until {\"success\": true}. Output the complete proof.
"
```

### Check Task Status

```bash
codex cloud status <task_id>
```

### Get Diff

```bash
codex cloud diff <task_id>
```

### Apply Changes

```bash
codex cloud apply <task_id>
```

## Server Maintenance

### Check Service Status

```bash
ssh root@108.61.166.134 "systemctl status rocq-verify nginx"
```

### View API Logs

```bash
ssh root@108.61.166.134 "tail -f /var/log/nginx/access.log"
```

### Restart Services

```bash
ssh root@108.61.166.134 "systemctl restart rocq-verify nginx"
```

### API Script Location

```
/home/coq-api/verify_api.py
```

## Troubleshooting

### Cloudflare Rate Limiting

If you get 403 errors from `codex cloud status`, your IP is rate-limited by Cloudflare. Options:
- Wait 15-60 minutes
- Use a VPN
- Check task status in browser: `https://chatgpt.com/codex/tasks/<task_id>`

### Connection Refused

If Codex Cloud can't reach the server:
1. Check nginx is running: `systemctl status nginx`
2. Check firewall: `ufw status` (port 80 must be open)
3. Test locally: `curl http://108.61.166.134/health`

### Proof Compilation Fails

Check the `stderr` field in the API response for Rocq error messages. Common issues:
- Missing imports
- Wrong file paths (must be `Plinko/Specs/<name>.v`)
- Tactic failures

## Example: Successful Proof

The `sr_inverse_range` lemma was proved using this setup:

1. Submitted task with 3 parallel attempts
2. Codex agents called verification API ~20 times (visible in nginx logs)
3. Task completed with working proof
4. Applied diff locally, verified with `make`

## Files

| File | Description |
|------|-------------|
| `/home/coq-api/verify_api.py` | Python HTTP API |
| `/etc/nginx/sites-available/rocq-verify` | Nginx config |
| `/etc/systemd/system/rocq-verify.service` | Systemd service |
