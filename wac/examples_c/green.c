// From: https://rosettacode.org/wiki/OpenGL#C

#include <stdio.h>
#include <stdlib.h>
#include <GL/gl.h>
#include <GL/glut.h>
#include <unistd.h>

int main(int argc, char *argv[])
{
  glutInit(&argc, argv);
  glutInitWindowSize(640, 480);
  glutCreateWindow("Green");

  glClearColor(0.3,0.5,0.3,0.0);
  glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
  glFlush();

  sleep(2);

  return EXIT_SUCCESS;
}
