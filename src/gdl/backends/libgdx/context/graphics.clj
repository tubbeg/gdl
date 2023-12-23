(ns gdl.backends.libgdx.context.graphics
  (:require gdl.context
            [gdl.graphics.color :as color]
            [gdl.backends.libgdx.utils.reflect :refer [bind-roots]])
  (:import com.badlogic.gdx.Gdx
           (com.badlogic.gdx.graphics Color Pixmap)))

(extend-type gdl.context.Context
  gdl.context/Graphics
  (delta-time [_]
    (.getDeltaTime Gdx/graphics))

  (frames-per-second [_]
    (.getFramesPerSecond Gdx/graphics))

  ; https://libgdx.com/wiki/input/cursor-visibility-and-catching
  (->cursor [_ file]
    (.newCursor Gdx/graphics
                (Pixmap. (.internal Gdx/files file))
                0
                0))

  (set-cursor! [_ cursor]
    (.setCursor Gdx/graphics cursor)))

(bind-roots "com.badlogic.gdx.graphics.Color"
            'com.badlogic.gdx.graphics.Color
            "gdl.graphics.color")
