(ns gdx.asset-manager
  (:require [gdx.app :as app]
            [gdx.files :as files])
  (:import [com.badlogic.gdx.assets AssetManager]
           [com.badlogic.gdx.audio Sound]
           [com.badlogic.gdx.graphics Texture]
           [com.badlogic.gdx.graphics.g2d TextureRegion]))

(def ^:private assets-folder "resources/")
(def ^:private sounds-subfolder "sounds/")
(def ^:private sound-files-extensions #{"wav"})
(def ^:private image-files-extensions #{"png" "bmp"})

; TODO
; com.badlogic.gdx.assets.loaders.SynchronousAssetLoader
; what is this ? what I am doing already?

(app/defmanaged
  ^{:private true
    :tag AssetManager
    :dispose true} asset-manager (AssetManager.))

(defn- load-assets [file-extensions klass]
  (doseq [file (files/recursively-search-files assets-folder file-extensions)]
    (.load asset-manager file klass)))

(defn- get-asset [file klass]
  (.get asset-manager ^String file ^Class klass))

(app/on-create
 (load-assets sound-files-extensions Sound)
 (load-assets image-files-extensions Texture)
 (.finishLoading asset-manager))

(app/defmanaged ^Sound file->sound
  (memoize
   (fn [file]
     (get-asset (str sounds-subfolder file) Sound))))

(app/defmanaged file->texture
   (memoize
    (fn [file & [x y w h]]
      (let [^Texture texture (get-asset file Texture)]
        (if (and x y w h)
          (TextureRegion. texture (int x) (int y) (int w) (int h))
          (TextureRegion. texture))))))
