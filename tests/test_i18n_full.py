"""
tests/test_i18n_full.py — validation of i18n coverage & translation safety

Goals:
  ✅ Ensure all translation keys exist and are well-formed.
  ✅ Check every supported language (EN, IT) returns a non-empty string.
  ✅ Verify .format() placeholders never crash.
  ✅ Ensure fallbacks (missing key/lang) are safe and human-readable.
"""

import re
import pytest
from i18n import t, set_default_lang, get_default_lang, LANGS, _MESSAGES


@pytest.mark.parametrize("lang", LANGS)
def test_all_keys_have_translations(lang: str):
    """Every translation key must produce a non-empty string for the given language."""
    set_default_lang(lang)
    for key, entry in _MESSAGES.items():
        value = t(key)
        assert isinstance(value, str), f"Translation for key '{key}' ({lang}) is not a string."
        assert value.strip(), f"Translation for key '{key}' ({lang}) is empty."


def test_safe_fallback_for_missing_key():
    """Missing keys should safely return the key itself."""
    set_default_lang("en")
    result = t("UNKNOWN_KEY_EXAMPLE")
    assert result == "UNKNOWN_KEY_EXAMPLE", "Missing keys should return the key name itself."


@pytest.mark.parametrize("key", ["OK_CREATED", "ERR_BIN_ARITY", "ERR_PSI", "ERR_MINIDSL"])
def test_placeholders_format_safely(key: str):
    """Placeholders (e.g., {idx}, {op}, {err}) should format safely and never raise."""
    set_default_lang("en")
    formatted = t(key, idx=42, op="AND", err="syntax error")
    assert isinstance(formatted, str)
    assert "{" not in formatted, "Unreplaced placeholder found in formatted string"


def test_safe_fallback_for_missing_language():
    """Missing language should fallback to English text."""
    fake_lang = "xx"
    set_default_lang(fake_lang)
    result = t("APP_TITLE")
    assert "Auto-Z3" in result, "Fallback to English failed for missing language."


def test_no_duplicate_keys():
    """Ensure translation keys are unique."""
    keys = list(_MESSAGES.keys())
    assert len(keys) == len(set(keys)), "Duplicate translation keys found."


def test_no_unwanted_html_or_tags():
    """Detect accidental HTML or markup inside translations."""
    pattern = re.compile(r"<[^>]+>")
    for lang in LANGS:
        for key, entry in _MESSAGES.items():
            val = entry.get(lang, "")
            assert not pattern.search(val), f"Unexpected HTML markup in '{key}' ({lang})"


def test_reset_default_language_to_english():
    """Ensure we can reset to default safely after switching."""
    set_default_lang("it")
    assert get_default_lang() == "it"
    set_default_lang("en")
    assert get_default_lang() == "en"
