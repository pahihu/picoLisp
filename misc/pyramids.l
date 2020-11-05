# 26oct20abu
# 27jul10jk
# (c) Jon Kleiser

# An OpenGL demo showing twelve pyramids chained together.
# The chain folds and unfolds. When completely folded, it is the shape of a cube.

(load "@lib/openGl.l")

(symbols '(openGl pico))

(setq *WinWidth 790  *WinHeight 480)
(setq *AngleX 0.0  *AngleY 0.0)
(setq *LastX 0  *LastY 0)
(setq *Sin45 0.70710678)
(setq *FoldTime 0.0)

(de initGL (Width Height)
   (glClearColor 0.6 0.8 0.9 0)  # the background color
   (glClearDepth 1.0)
   (glDepthFunc GL_LESS)
   (glEnable GL_DEPTH_TEST)
   (glShadeModel GL_FLAT)

   (glEnable GL_LIGHTING)
   (glEnable GL_LIGHT0)
   (glDisable GL_CULL_FACE)
   (glEnable GL_BLEND)
   (glBlendFunc GL_SRC_ALPHA GL_ONE_MINUS_SRC_ALPHA)
   (glColorMaterial GL_FRONT_AND_BACK GL_AMBIENT_AND_DIFFUSE)
   (glEnable GL_COLOR_MATERIAL)

   (glMatrixMode GL_PROJECTION)
   (glLoadIdentity)
   (gluPerspective 45.0 (*/ Width 1.0 Height) 0.1 100.0)
   (glMatrixMode GL_MODELVIEW) )

(glutInit)
# Set display mode: RGBA color, Double buffer, Alpha support, Depth buffer
(glutInitDisplayMode (| GLUT_RGBA GLUT_DOUBLE GLUT_ALPHA GLUT_DEPTH))
(glutInitWindowSize *WinWidth *WinHeight)
(glutInitWindowPosition 10 50)
(glutCreateWindow "Folding Pyramids")

(initGL *WinWidth *WinHeight)

(de drawPyramid ()
   (glBegin GL_TRIANGLES)
   (glNormal3f (- *Sin45) 0.0 *Sin45)
   (glVertex3f 1.0 1.0 1.0)  # 0
   (glVertex3f 0.0 2.0 0.0)  # 1
   (glVertex3f 0.0 0.0 0.0)  # 2

   (glNormal3f 0.0 (- *Sin45) *Sin45)
   (glVertex3f 1.0 1.0 1.0)  # 0
   (glVertex3f 0.0 0.0 0.0)  # 2
   (glVertex3f 2.0 0.0 0.0)  # 3

   (glNormal3f *Sin45 *Sin45 0.0)
   (glVertex3f 1.0 1.0 1.0)  # 0
   (glVertex3f 2.0 0.0 0.0)  # 3
   (glVertex3f 0.0 2.0 0.0)  # 1

   (glNormal3f 0.0 0.0 -1.0)
   (glVertex3f 2.0 0.0 0.0)  # 3
   (glVertex3f 0.0 0.0 0.0)  # 2
   (glVertex3f 0.0 2.0 0.0)  # 1
   (glEnd) )

(displayPrg
   (setq PyrRot (+ (*/ (cos *FoldTime) 45.0 1.0) 45.0))
   (glClear (| GL_COLOR_BUFFER_BIT GL_DEPTH_BUFFER_BIT))
   (glLoadIdentity)
   (glTranslatef 0.0 -0.4 -11.0)
   (glRotatef *AngleX 1 0 0)
   (glRotatef *AngleY 0 1 0)
   (glRotatef (- (/ PyrRot 2)) 0 1 0)
   (glPushMatrix)

   (glColor4f 1.0 0.7 0.0 1.0)  # yellow
   (drawPyramid)  # 1

   (glRotatef PyrRot 0 1 0)
   (glRotatef 90.0 0 0 1)
   (glColor4f 0.4 0.0 0.6 1.0)  # violet
   (drawPyramid)  # 2

   (glTranslatef 0.0 2.0 0.0)
   (glRotatef PyrRot 0 1 0)
   (glRotatef 180.0 0 0 1)
   (glColor4f 1.0 0.2 0.0 1.0)  # red
   (drawPyramid)  # 3

   (glRotatef (- PyrRot) 1 0 0)
   (glRotatef -90.0 0 0 1)
   (glColor4f 1.0 0.7 0.0 1.0)  # yellow
   (drawPyramid)  # 4

   (glTranslatef 2.0 0.0 0.0)
   (glRotatef (- PyrRot) 1 0 0)
   (glRotatef 180.0 0 0 1)
   (glColor4f 0.4 0.0 0.6 1.0)  # violet
   (drawPyramid)  # 5

   (glRotatef PyrRot 0 1 0)
   (glRotatef 90.0 0 0 1)
   (glColor4f 1.0 0.2 0.0 1.0)  # red
   (drawPyramid)  # 6

   (glTranslatef 0.0 2.0 0.0)
   (glRotatef PyrRot 0 1 0)
   (glRotatef 180.0 0 0 1)
   (glColor4f 1.0 0.7 0.0 1.0)  # yellow
   (drawPyramid)  # 7

   (glPopMatrix)

   (glTranslatef 2.0 0.0 0.0)
   (glRotatef (- PyrRot) 1 0 0)
   (glRotatef 180.0 0 0 1)
   (glColor4f 1.0 0.2 0.0 1.0)  # red
   (drawPyramid)  # 12

   (glRotatef PyrRot 0 1 0)
   (glRotatef 90.0 0 0 1)
   (glColor4f 0.4 0.0 0.6 1.0)  # violet
   (drawPyramid)  # 11

   (glTranslatef 0.0 2.0 0.0)
   (glRotatef PyrRot 0 1 0)
   (glRotatef 180.0 0 0 1)
   (glColor4f 1.0 0.7 0.0 1.0)  # yellow
   (drawPyramid)  # 10

   (glRotatef (- PyrRot) 1 0 0)
   (glRotatef -90.0 0 0 1)
   (glColor4f 1.0 0.2 0.0 1.0)  # red
   (drawPyramid)  # 9

   (glTranslatef 2.0 0.0 0.0)
   (glRotatef (- PyrRot) 1 0 0)
   (glRotatef 180.0 0 0 1)
   (glColor4f 0.4 0.0 0.6 1.0)  # violet
   (drawPyramid)  # 8

   (glFlush)
   (glutSwapBuffers)
   0 )

(reshapeFunc
   '((Width Height)
      (glViewport 0 0 Width Height)
      (glMatrixMode GL_PROJECTION)
      (glLoadIdentity)
      (gluPerspective 45.0 (*/ Width 1.0 Height) 0.1 100.0)
      (glMatrixMode GL_MODELVIEW)
      0 ) )

(mouseFunc
   '((Btn State X Y)
      (setq *LastX X *LastY Y)
      0 ) )

(motionFunc '((X Y)
   (inc '*AngleX (* (- Y *LastY) 1.0))
   (inc '*AngleY (* (- X *LastX) 1.0))
   (setq *LastX X *LastY Y)
   #(println "motionFunc" X Y)
   (glutPostRedisplay)
   0 ) )

(de startTimer ()
   (timerFunc 40 myTimer 0)
   0 )

(de myTimer (Val)
   (inc '*FoldTime 0.02)
   (glutPostRedisplay)
   (startTimer) )

(startTimer)
(glutMainLoop)
