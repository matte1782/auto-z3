import streamlit as st


def inject_theme():
    st.markdown(
        """
    <style>
      /* look & feel ispirato a HIG: aria, gerarchia, focus sulle azioni */
      .main > div { padding-top: 0.5rem; }
      h1, h2, h3 { font-weight: 600; letter-spacing: -0.01em; }
      .stButton>button { border-radius: 10px; padding: 0.5rem 0.9rem; }
      .ok-badge { background:#E6FFF2; color:#05603A; border-radius: 999px; padding: 0.15rem 0.6rem; font-weight:600; }
      .bad-badge { background:#FFE6E6; color:#7A0916; border-radius: 999px; padding: 0.15rem 0.6rem; font-weight:600; }
      .info-badge{ background:#EEF2FF; color:#1E3A8A; border-radius: 999px; padding: 0.15rem 0.6rem; font-weight:600; }
      code { font-size: 0.92rem; }
    </style>
    """,
        unsafe_allow_html=True,
    )
