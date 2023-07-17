(ns gdx.assets
  (:require [gdx.app :as app]
            [gdx.files :as files])
  (:import com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.graphics.Texture
           com.badlogic.gdx.graphics.g2d.TextureRegion))

; TODO make public and just set-var-root #'gdx.assets/assets-folder "test/resources" ?
(def ^:private assets-folder "resources/")
(def ^:private sounds-subfolder "sounds/")
(def ^:private sound-files-extensions #{"wav"})
(def ^:private image-files-extensions #{"png" "bmp"})

; TODO
; com.badlogic.gdx.assets.loaders.SynchronousAssetLoader
; what is this ? what I am doing already?
; -> checkout libgdx project

; => add bitmapfont, freetypeloader, tmx files ?
; no need to handle disposing

(app/defmanaged
  ^{:private true
    :tag AssetManager
    :dispose true} manager (AssetManager.))

(defn- load-assets [file-extensions klass]
  (doseq [file (files/recursively-search-files assets-folder file-extensions)]
    (.load manager file klass)))

(defn- get-asset [file klass]
  (.get manager ^String file ^Class klass))

(app/on-create
 (load-assets sound-files-extensions Sound)
 (load-assets image-files-extensions Texture)
 (.finishLoading manager))

; TODO memoized necessary? get-asset is already memoized? for sound not necessary...
; -=> then defmanaged also not necessary anymore.

(app/defmanaged ^Sound get-sound
  (memoize
   (fn [file]
     (get-asset (str sounds-subfolder file) Sound))))

; TODO texture-region stuff move to graphics/images
; here just get-texture ! simple (maybe no memoization needed at all ..)
(app/defmanaged get-texture
   (memoize
    (fn [file & [x y w h]]
      (let [^Texture texture (get-asset file Texture)]
        (if (and x y w h)
          (TextureRegion. texture (int x) (int y) (int w) (int h))
          (TextureRegion. texture))))))
