import React from 'react';
import { styled } from '@material-ui/core/styles';

const Wrapper = styled('div')(({ width }: { width: number }) => ({
  width: width,
  display: 'flex',
}));

const InnerWrapper = styled('div')(({ theme }) => ({
  position: 'relative',
  flexGrow: 1,
  backgroundColor: theme.palette.grey[100],
}));

const Dragger = styled('div')(({ theme }) => ({
  width: '5px',
  cursor: 'ew-resize',
  backgroundColor: theme.palette.grey[300],
}));

const MIN_WIDTH = 300;

export default function EventListWrapper({
  children,
}: {
  children: React.ReactNode;
}) {
  const [width, setWidth] = React.useState(
    // Equivalent to `width: 40%; max-width: 500px;`
    Math.min(Math.floor(window.innerWidth * 0.4), 500)
  );

  const handleMouseDown = React.useCallback(() => {
    document.addEventListener('mouseup', handleMouseUp, true);
    document.addEventListener('mousemove', handleMouseMove, true);
  }, []);

  const handleMouseUp = React.useCallback(() => {
    document.removeEventListener('mouseup', handleMouseUp, true);
    document.removeEventListener('mousemove', handleMouseMove, true);
  }, []);

  const handleMouseMove = React.useCallback((event) => {
    event.preventDefault();
    setWidth(Math.max(MIN_WIDTH, window.innerWidth - event.clientX));
  }, []);

  return (
    <Wrapper width={width}>
      <Dragger onMouseDown={handleMouseDown} />
      <InnerWrapper>{children}</InnerWrapper>
    </Wrapper>
  );
}
