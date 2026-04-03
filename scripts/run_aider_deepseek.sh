#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ENV_FILE="${AIDER_ENV_FILE:-$ROOT_DIR/.env.aider.deepseek}"
AIDER_BIN="${AIDER_BIN:-$HOME/.local/bin/aider}"
MODEL_DEFAULT="${AIDER_MODEL:-openai/deepseek-chat}"

if [[ ! -f "$ENV_FILE" ]]; then
  echo "Missing env file: $ENV_FILE" >&2
  echo "Copy $ROOT_DIR/.env.aider.deepseek.example to $ROOT_DIR/.env.aider.deepseek and fill in your key." >&2
  exit 1
fi

set -a
source "$ENV_FILE"
set +a

if [[ -z "${OPENAI_API_BASE:-}" ]]; then
  echo "OPENAI_API_BASE is not set" >&2
  exit 1
fi

if [[ -z "${OPENAI_API_KEY:-}" ]]; then
  echo "OPENAI_API_KEY is not set" >&2
  exit 1
fi

exec "$AIDER_BIN" \
  --model "${AIDER_MODEL:-$MODEL_DEFAULT}" \
  --openai-api-base "$OPENAI_API_BASE" \
  --openai-api-key "$OPENAI_API_KEY" \
  "$@"
