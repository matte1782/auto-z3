# color_maps/plotly_preview.py
import json

import pandas as pd
import plotly.express as px
import streamlit as st


def render_plotly_preview(path):
    with open(path, encoding="utf-8") as f:
        gj = json.load(f)
    rows = []
    for ft in gj["features"]:
        rows.append(dict(ISO_A3=ft["properties"]["ISO_A3"], NAME=ft["properties"]["NAME"]))
    df = pd.DataFrame(rows)

    fig = px.choropleth(
        df,
        geojson=gj,
        locations="ISO_A3",
        featureidkey="properties.ISO_A3",
        color=None,
        hover_name="NAME",
        projection="mercator",
    )
    fig.update_geos(fitbounds="locations", visible=False)
    fig.update_layout(margin=dict(l=0, r=0, t=0, b=0), height=560)
    st.plotly_chart(fig, use_container_width=True)
