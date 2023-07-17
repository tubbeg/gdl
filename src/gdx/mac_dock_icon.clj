; TODO if this is required on windows/linux will break?
; only require @ mac ?
(ns ^:no-doc gdx.mac-dock-icon
  (:require [clojure.java.io :as io])
  (:import com.apple.eawt.Application
           javax.imageio.ImageIO))

; TODO :
; -> move to libgdx lwjgl3 backend code?
; https://github.com/libgdx/libgdx/blob/75612dae1eeddc9611ed62366858ff1d0ac7898b/backends/gdx-backend-lwjgl3/src/com/badlogic/gdx/backends/lwjgl3/Lwjgl3Window.java#L281

; https://github.com/glfw/glfw/issues/2041

; Alternative:
; java.awt.Toolkit
; java.awt.Taskbar

;  private static void updateDockIconForMacOs() {
;        if (SharedLibraryLoader.isMac) {
;            try {
;
;                Toolkit defaultToolkit = Toolkit.getDefaultToolkit();
;                // icon.png is in assets
;                final URL imageResource = DesktopLauncher.class.getClassLoader().getResource("icon.png");
;                final Image image = defaultToolkit.getImage(imageResource);
;                Taskbar taskbar = Taskbar.getTaskbar();
;                taskbar.setIconImage(image);
;            } catch (Throwable throwable) {
;                throwable.printStackTrace()
;            }
;        }
;    }

; setWindowIcon not working libgdx if mac :
; https://github.com/libgdx/libgdx/blob/master/backends/gdx-backend-lwjgl3/src/com/badlogic/gdx/backends/lwjgl3/Lwjgl3Window.java#L159
(defn set-mac-os-dock-icon []

  ; https://github.com/LWJGL/lwjgl3/issues/68
  ; This is because using those objects will cause the AWT to run it's event loop, and on OSX, the main thread is already used by GLFW. The solution is to set the headless property of the AWT to true.
  ; Set that property before creating the window, then create the window. Also note that you have to create the fonts or the resources only after the window is created.

  ; do set only once in case of
  ; clojure.tools.namespace.repl/refresh-all
  ; otherwise it gives a console warning every app start
  (when-not (= (System/getProperty "java.awt.headless") "true")
    (System/setProperty "java.awt.headless" "true"))

  (let [image (ImageIO/read (io/file (str "resources/logo.png")))]
    (.setDockIconImage (Application/getApplication) image)))
